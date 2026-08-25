#!/usr/bin/env python3
r"""Formalize Mathematica `LinearRecurrence[...]` %t lines into Lean 4 + Mathlib.

This script walks OEIS `.seq` files (or queries the `program` table of
`Metadata/oeis.db`) for Mathematica blocks containing calls of the form

    LinearRecurrence[{2, 1, -2}, {3, 5, 13}, 50] (* G. C. Greubel, Jun 27 2018 *)

For each such call it generates:

  * `LOEIS/<bucket>/<A-number>/Equiv_<hash>.lean`  — the Lean definition, built
    from `Mathlib.Algebra.LinearRecurrence.LinearRecurrence.mk` and
    `LinearRecurrence.mkSol`;
  * a temporary check module under `Check/LinearRecurrence/B<n>/` that
    `#eval`s the formula against the OEIS terms;

compiles them with `lake build`, and on success marks the formula as
`STATUS_VERIFIED` in `oeis.db` (inserting into `formalization_item` and
updating the `formula` table, matching what the Maple pipeline does).

Usage:
    python Scripts/LinearRecurrenceWolfram.py [--seq-dir DIR] [--db PATH]
                                              [--bucket A000]... [--seq A000001]...
                                              [--terms N] [--timeout SECONDS]
                                              [--limit N] [--dry-run] [--keep-check-files]
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import sqlite3
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_DB = REPO_ROOT / "Metadata" / "oeis.db"
DEFAULT_LOEIS = REPO_ROOT / "LOEIS"
DEFAULT_CHECK = REPO_ROOT / "Check"
DEFAULT_SEQ_DIR = REPO_ROOT / "oeisdata" / "seq"
TEMPLATE_PATH = Path(__file__).resolve().parent / "Templates" / "LinearRecurrenceWolfram.lean"

LOEIS_LIB = "LOEIS"
CHECK_LIB = "Check"

# ---------------------------------------------------------------------------
# Regular expressions
# ---------------------------------------------------------------------------

# Matches a single %t record line:  %t A000001 <content>
RECORD_LINE = re.compile(r"^%t\s+(A\d{6})\s+(.*)$")

# Matches a LinearRecurrence call.
LINEAR_REC = re.compile(
    r"LinearRecurrence\s*\[\s*"
    r"\{(?P<coeffs>[^}]*)\}\s*,\s*"
    r"\{(?P<init>[^}]*)\}\s*"
    r"(?:,\s*(?P<range>[^)\]]*?))?"
    r"\s*\]\s*"
    r"(?:\(\*\s*(?P<credit>[^*]*?)\s*\*\))?",
)

# Author / date inside a Mathematica comment, e.g.
#   (* _G. C. Greubel_, Jun 27 2018 *)
#   (* Harvey P. Dale, Aug 02 2015 *)
CREDIT_RE = re.compile(
    r"(?:_?(?P<author>[^,_*]+?)_?)\s*,\s*"
    r"(?P<date>[A-Z][a-z]{2,8}\s+\d{1,2}\s+\d{4})"
)

# A-number anywhere in a line.
ANUM_RE = re.compile(r"\b(A\d{6})\b")

# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------


@dataclass
class LRFormula:
    """One parsed `LinearRecurrence[...]` call."""

    oeis_name: str
    coeffs: list[int]
    init: list[int]
    range_arg: str
    author: str = ""
    date: str = ""
    original_text: str = ""
    block_text: str = ""
    source_hash: str = ""
    title: str = ""
    offset: int = 0
    terms: list[str] = field(default_factory=list)
    formula_hash: str = ""


# ---------------------------------------------------------------------------
# Hashing — same algorithm as the Maple pipeline (blake2b, 8 bytes → 16 hex)
# ---------------------------------------------------------------------------

def snippet_hash(text: str) -> str:
    return hashlib.blake2b(text.encode("utf-8"), digest_size=8).hexdigest()


def block_hash(text: str) -> str:
    """Matches `Oeis.formulaHash` in Lean: `String.hash` is not portable across
    runs, but the `program.hash` column stores the same `blake2b` digest used
    by the Python side (see `Scripts/OeisIngest/Parse.lean`).  We hash the
    *trimmed* block text to match how it is stored."""
    return snippet_hash(text.strip())


# ---------------------------------------------------------------------------
# Parsing helpers
# ---------------------------------------------------------------------------

def _parse_int_list(raw: str) -> list[int] | None:
    """Parses `1, -2, 3` into `[1, -2, 3]`.  Returns None on any non-integer."""
    parts = [p.strip() for p in raw.split(",")]
    out: list[int] = []
    for p in parts:
        if not p:
            continue
        try:
            out.append(int(p))
        except ValueError:
            return None
    return out


def _parse_credit(credit: str | None) -> tuple[str, str]:
    if not credit:
        return "", ""
    m = CREDIT_RE.search(credit)
    if not m:
        return credit.strip(), ""
    author = m.group("author").strip().strip("_")
    date = m.group("date").strip()
    return author, date


def parse_block(oeis_name: str, block_text: str) -> list[LRFormula]:
    """Extract all `LinearRecurrence[...]` calls from one %t block."""
    results: list[LRFormula] = []
    for m in LINEAR_REC.finditer(block_text):
        coeffs = _parse_int_list(m.group("coeffs"))
        init = _parse_int_list(m.group("init"))
        if coeffs is None or init is None:
            continue
        if len(coeffs) != len(init):
            continue
        if len(coeffs) == 0:
            continue
        range_arg = (m.group("range") or "").strip()
        author, date = _parse_credit(m.group("credit"))
        original_text = m.group(0).strip()
        results.append(
            LRFormula(
                oeis_name=oeis_name,
                coeffs=coeffs,
                init=init,
                range_arg=range_arg,
                author=author,
                date=date,
                original_text=original_text,
                block_text=block_text,
                source_hash=block_hash(block_text),
                formula_hash=snippet_hash(original_text),
            )
        )
    return results


# ---------------------------------------------------------------------------
# .seq file scanning
# ---------------------------------------------------------------------------

def scan_seq_file(path: Path) -> list[tuple[str, str, str]]:
    """Return list of (A-number, %t-block-text, source_file)."""
    blocks: dict[str, list[str]] = {}
    try:
        content = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return []
    current_anum = ""
    for raw_line in content.splitlines():
        line = raw_line.rstrip()
        m = RECORD_LINE.match(line)
        if m:
            anum, content_text = m.group(1), m.group(2)
            blocks.setdefault(anum, []).append(content_text)
            current_anum = anum
        elif line.startswith("%") and len(line) > 1 and line[1] != "t":
            current_anum = ""
    out: list[tuple[str, str, str]] = []
    for anum, lines in blocks.items():
        text = "\n".join(lines).strip()
        if text:
            out.append((anum, text, str(path)))
    return out


def collect_seq_files(
    seq_dir: Path,
    buckets: list[str] | None = None,
    seqs: list[str] | None = None,
) -> list[Path]:
    files: list[Path] = []
    if not seq_dir.is_dir():
        return files
    seq_set = {s.upper() for s in seqs} if seqs else None
    for bucket_dir in sorted(seq_dir.iterdir()):
        if not bucket_dir.is_dir():
            continue
        if buckets and bucket_dir.name not in buckets:
            continue
        for f in sorted(bucket_dir.iterdir()):
            if f.suffix != ".seq":
                continue
            if seq_set is not None and f.stem.upper() not in seq_set:
                continue
            files.append(f)
    return files


def scan_from_seq_files(
    seq_dir: Path,
    buckets: list[str] | None,
    seqs: list[str] | None,
) -> list[LRFormula]:
    formulas: list[LRFormula] = []
    files = collect_seq_files(seq_dir, buckets, seqs)
    print(f"Scanning {len(files)} .seq files under {seq_dir} ...", file=sys.stderr)
    for path in files:
        meta = parse_seq_metadata(path)
        for anum, block_text, _ in scan_seq_file(path):
            parsed = parse_block(anum, block_text)
            if anum in meta:
                title, offset, terms = meta[anum]
                for f in parsed:
                    f.title = title
                    f.offset = offset
                    f.terms = terms
            formulas.extend(parsed)
    return formulas


# ---------------------------------------------------------------------------
# Database scanning (when .seq files are not available or to enrich metadata)
# ---------------------------------------------------------------------------

def connect_db(db_path: Path) -> sqlite3.Connection | None:
    if not db_path.is_file():
        return None
    try:
        conn = sqlite3.connect(str(db_path), timeout=30.0)
        conn.row_factory = sqlite3.Row
        # Verify this is actually a SQLite database (LFS pointers will fail here).
        conn.execute("SELECT count(*) FROM sqlite_master").fetchone()
        return conn
    except (sqlite3.DatabaseError, sqlite3.OperationalError):
        return None


def scan_from_db(
    conn: sqlite3.Connection,
    buckets: list[str] | None = None,
    seqs: list[str] | None = None,
) -> list[LRFormula]:
    where = ["p.language = ?", "p.text LIKE '%LinearRecurrence%'"]
    params: list[object] = ["mathematica"]
    if seqs:
        where.append("p.oeis_name IN (%s)" % ",".join("?" * len(seqs)))
        params.extend(s.upper() for s in seqs)
    if buckets:
        where.append(
            "(%s)" % " OR ".join("substr(p.oeis_name,1,4)=?" for _ in buckets)
        )
        params.extend(buckets)
    sql = (
        "SELECT p.oeis_name, p.text, p.hash, s.title, s.\"offset\", s.data "
        "FROM program p JOIN sequence s ON s.name = p.oeis_name "
        "WHERE " + " AND ".join(where)
    )
    formulas: list[LRFormula] = []
    for row in conn.execute(sql, params):
        parsed = parse_block(row["oeis_name"], row["text"])
        title = row["title"] or ""
        offset = int(row["offset"] or 0)
        terms = json.loads(row["data"] or "[]", parse_int=str)
        for f in parsed:
            f.title = title
            f.offset = offset
            f.terms = terms
            f.source_hash = row["hash"] or f.source_hash
        formulas.extend(parsed)
    return formulas


def enrich_from_db(formulas: list[LRFormula], conn: sqlite3.Connection) -> None:
    """Fill in title / offset / terms from the DB for formulas found via .seq scan."""
    if not formulas:
        return
    names = sorted({f.oeis_name for f in formulas})
    placeholders = ",".join("?" for _ in names)
    sql = (
        f'SELECT name, title, "offset", data FROM sequence WHERE name IN ({placeholders})'
    )
    info: dict[str, tuple[str, int, list[str]]] = {}
    for row in conn.execute(sql, names):
        info[row["name"]] = (
            row["title"] or "",
            int(row["offset"] or 0),
            json.loads(row["data"] or "[]", parse_int=str),
        )
    for f in formulas:
        if f.oeis_name in info:
            f.title, f.offset, f.terms = info[f.oeis_name]


# ---------------------------------------------------------------------------
# Sequence metadata helpers (when no DB is available — parse the .seq file)
# ---------------------------------------------------------------------------

def parse_seq_metadata(path: Path) -> dict[str, tuple[str, int, list[str]]]:
    """Parse %N, %O, %S/%T/%U lines from a .seq file for all A-numbers in it."""
    out: dict[str, dict] = {}
    cur = ""
    s_terms: dict[str, str] = {}
    t_terms: dict[str, str] = {}
    u_terms: dict[str, str] = {}
    try:
        for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
            m = re.match(r"^%([A-Z])\s+(A\d{6})\s+(.*)$", line.rstrip())
            if not m:
                continue
            tag, anum, content = m.group(1), m.group(2), m.group(3)
            cur = anum
            entry = out.setdefault(anum, {"title": "", "offset": 0})
            if tag == "N":
                if not entry["title"]:
                    entry["title"] = content
            elif tag == "O":
                parts = [p.strip() for p in content.split(",")]
                if parts and parts[0].lstrip("-").isdigit():
                    entry["offset"] = int(parts[0])
            elif tag == "S":
                s_terms[anum] = s_terms.get(anum, "") + content
            elif tag == "T":
                t_terms[anum] = t_terms.get(anum, "") + content
            elif tag == "U":
                u_terms[anum] = u_terms.get(anum, "") + content
    except OSError:
        return {}
    result: dict[str, tuple[str, int, list[str]]] = {}
    for anum, entry in out.items():
        raw = ",".join([s_terms.get(anum, ""), t_terms.get(anum, ""),
                        u_terms.get(anum, "")])
        terms = [t.strip() for t in raw.split(",") if t.strip()]
        result[anum] = (entry["title"], entry["offset"], terms)
    return result


# ---------------------------------------------------------------------------
# Lean code generation
# ---------------------------------------------------------------------------

def _bucket(name: str) -> str:
    return name[:4]


def _arg_type(offset: int) -> str:
    if offset == 0:
        return "Nat"
    if offset == 1:
        return "PNat"
    if offset > 1:
        return "{" + f"n : Nat // {offset} ≤ n" + "}"
    return "{" + f"n : Int // {offset} ≤ n" + "}"


def _formula_body(offset: int, order: int) -> str:
    """Return the body of `formula`, with leading indentation."""
    if offset == 0:
        return "  fun n => linearrec.mkSol init n"
    if offset == 1:
        return "  fun n => linearrec.mkSol init (n.val - 1)"
    if offset > 1:
        return f"  fun n => linearrec.mkSol init (n.val - {offset})"
    # offset < 0: IntSub
    return f"  fun n => linearrec.mkSol init ((n.val - ({offset} : Int)).toNat)"


def _fin_matches(values: list[int], indent: str = "    ") -> str:
    """Generate `| i => v` lines for a Fin n → Int function."""
    lines = []
    for i, v in enumerate(values):
        if i == 0:
            continue  # already handled by `| 0 =>` in the template
        lines.append(f"{indent}| {i} => {v}")
    return "\n".join(lines)


def _ret_type(terms: list[str]) -> str:
    """Return `Int` if any term is negative, else `Nat`."""
    return "Int" if any(t.startswith("-") for t in terms) else "Nat"


def _formula_eq_rhs(f: LRFormula) -> str:
    """Right-hand side of the `formula_eq` theorem, with coercion if needed."""
    ret = _ret_type(f.terms)
    if ret == "Int":
        return f"({f.oeis_name} n : Int)"
    else:
        # formula returns Int; the main def returns Nat
        return f"({f.oeis_name} n : Int)"


def _sanitize_doc(s: str) -> str:
    return s.replace("-/", "- /").replace("/-", "/ -")


def render_equiv(f: LRFormula, template: str) -> str:
    order = len(f.coeffs)
    coeff_matches = _fin_matches(f.coeffs)
    init_matches = _fin_matches(f.init)
    source_lines = "\n".join(
        "    " + _sanitize_doc(line) for line in f.original_text.splitlines()
    )
    # If there is only one coefficient/init, there are no extra match arms.
    if order == 1:
        coeff_matches = "    | _ => unreachable!"
        init_matches = "    | _ => unreachable!"
    else:
        coeff_matches += "\n    | _ => unreachable!"
        init_matches += "\n    | _ => unreachable!"

    return (
        template
        .replace("__BUCKET__", _bucket(f.oeis_name))
        .replace("__SEQNAME__", f.oeis_name)
        .replace("__HASH__", f.formula_hash)
        .replace("__TITLE__", _sanitize_doc(f.title))
        .replace("__ORDER__", str(order))
        .replace("__COEFF_0__", str(f.coeffs[0]))
        .replace("__COEFF_MATCHES__", coeff_matches)
        .replace("__INIT_0__", str(f.init[0]))
        .replace("__INIT_MATCHES__", init_matches)
        .replace("__ARG_TYPE__", _arg_type(f.offset))
        .replace("__FORMULA_BODY__", _formula_body(f.offset, order))
        .replace("__FORMULA_EQ_RHS__", _formula_eq_rhs(f))
        .replace("__SOURCE__", source_lines)
    )


def _index_literal(kind_offset: int, index: int, offset: int) -> str:
    if offset == 0:
        return f"({index} : Nat)"
    if offset == 1:
        return f"({index} : PNat)"
    if offset > 1:
        return f"(⟨{index}, by norm_num⟩ : {{n : Nat // {offset} ≤ n}})"
    return f"(⟨{index}, by norm_num⟩ : {{n : Int // {offset} ≤ n}})"


def render_check(f: LRFormula, batch_id: int, max_terms: int) -> str:
    """Render the temporary Check module that evaluates `formula` against OEIS data."""
    ns = f"{CHECK_LIB}.LinearRecurrence.B{batch_id}.{f.oeis_name}_{f.formula_hash}"
    equiv_mod = f"{LOEIS_LIB}.{_bucket(f.oeis_name)}.{f.oeis_name}.Equiv_{f.formula_hash}"
    count = min(max_terms, len(f.terms))
    terms = f.terms[:count]
    args = [
        _index_literal(f.offset + i, f.offset + i, f.offset)
        for i in range(count)
    ]
    expected = ", ".join(f"({t})" if t.startswith("-") else t for t in terms)
    actual = ",\n   ".join(f"((formula {a} : Int))" for a in args)
    return "\n".join([
        f"import {CHECK_LIB}.Basic",
        f"import {equiv_mod}",
        "",
        "/-! Generated validation module; deleted once the batch is recorded. -/",
        "",
        f"open {f.oeis_name}.Equiv_{f.formula_hash}",
        "",
        f"namespace {ns}",
        "",
        f'#eval Oeis.Check.report "{f.oeis_name}" ({f.offset})',
        f"  [{expected}]",
        f"  [{actual}]",
        "",
        f"end {ns}",
        "",
    ])


# ---------------------------------------------------------------------------
# lake build
# ---------------------------------------------------------------------------

DIAG_RE = re.compile(
    r"^(?:error|warning|info): (?:\./)?([^\s:]+\.lean):(\d+):(\d+): (.*)$"
)
CHECK_FAIL_RE = re.compile(r"OEIS_CHECK_FAIL\s+(A\d{6}):\s*(.*)$", re.MULTILINE)


def _lake_binary() -> str:
    found = shutil.which("lake")
    if found:
        return found
    candidate = Path.home() / ".elan" / "bin" / "lake"
    if candidate.exists():
        return str(candidate)
    raise RuntimeError("`lake` not found; install elan or add it to PATH")


@dataclass
class BuildResult:
    ok: bool
    timed_out: bool
    output: str
    per_file: dict[str, list[str]] = field(default_factory=dict)

    def diagnostics_for(self, *paths: str) -> list[str]:
        out: list[str] = []
        for p in paths:
            if not p:
                continue
            out.extend(self.per_file.get(p, []))
            # Also try just the file name and the path relative to cwd.
            if "/" in p:
                out.extend(self.per_file.get(p.split("/")[-1], []))
            out.extend(self.per_file.get(os.path.basename(p), []))
        # Deduplicate while preserving order.
        seen: set[str] = set()
        unique: list[str] = []
        for d in out:
            if d not in seen:
                seen.add(d)
                unique.append(d)
        return unique


def _attribute(output: str) -> dict[str, list[str]]:
    per_file: dict[str, list[str]] = {}
    current: list[str] | None = None
    for line in output.splitlines():
        m = DIAG_RE.match(line.strip())
        if m:
            kind, path = m.group(1), m.group(1)
            kind = line.strip().split(":", 1)[0]
            current = per_file.setdefault(path, []) if kind == "error" else None
            if current is not None:
                current.append(line.rstrip())
            continue
        if line.startswith((
            "✔", "✖", "⚠", "ℹ", "info:", "warning:", "trace:",
            "Build completed", "Some required targets",
        )):
            current = None
            continue
        if current is not None:
            current.append(line.rstrip())
    return per_file


def lake_build(targets: list[str], timeout: int) -> BuildResult:
    if not targets:
        return BuildResult(ok=True, timed_out=False, output="")
    env = dict(os.environ)
    env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env.get('PATH', '')}"
    try:
        proc = subprocess.run(
            [_lake_binary(), "build", *targets],
            cwd=str(REPO_ROOT),
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        out = (exc.stdout or "") + (exc.stderr or "")
        if isinstance(out, bytes):
            out = out.decode("utf-8", "replace")
        return BuildResult(ok=False, timed_out=True, output=out)
    output = proc.stdout + proc.stderr
    return BuildResult(
        ok=proc.returncode == 0,
        timed_out=False,
        output=output,
        per_file=_attribute(output),
    )


# ---------------------------------------------------------------------------
# Database update (mark as STATUS_VERIFIED)
# ---------------------------------------------------------------------------

MIGRATION_SQL = """
CREATE TABLE IF NOT EXISTS formalization_batch (
  id           INTEGER PRIMARY KEY AUTOINCREMENT,
  language     TEXT NOT NULL DEFAULT 'mathematica',
  model        TEXT NOT NULL DEFAULT '',
  status       TEXT NOT NULL DEFAULT 'BATCH_PENDING',
  oeis_names   TEXT NOT NULL DEFAULT '[]',
  attempts     INTEGER NOT NULL DEFAULT 0,
  max_attempts INTEGER NOT NULL DEFAULT 1,
  chat_history TEXT NOT NULL DEFAULT '[]',
  skill_text   TEXT NOT NULL DEFAULT '',
  last_error   TEXT NOT NULL DEFAULT '',
  usage        TEXT NOT NULL DEFAULT '{}',
  created_at   TEXT,
  updated_at   TEXT
);

CREATE TABLE IF NOT EXISTS formalization_item (
  id              INTEGER PRIMARY KEY AUTOINCREMENT,
  batch_id        INTEGER NOT NULL,
  oeis_name       TEXT NOT NULL,
  language        TEXT NOT NULL DEFAULT 'mathematica',
  source_hash     TEXT NOT NULL DEFAULT '',
  formula_hash    TEXT NOT NULL,
  original_text   TEXT NOT NULL DEFAULT '',
  span_start      INTEGER,
  span_end        INTEGER,
  computable      INTEGER NOT NULL DEFAULT 1,
  arg_kind        TEXT NOT NULL DEFAULT '',
  lean_code       TEXT NOT NULL DEFAULT '',
  lean_file       TEXT NOT NULL DEFAULT '',
  check_file      TEXT NOT NULL DEFAULT '',
  depends_on      TEXT NOT NULL DEFAULT '[]',
  status          TEXT NOT NULL DEFAULT 'STATUS_UNKNOWN',
  failure_kind    TEXT NOT NULL DEFAULT '',
  failure_points  TEXT NOT NULL DEFAULT '[]',
  compiler_output TEXT NOT NULL DEFAULT '',
  verified_upto   INTEGER NOT NULL DEFAULT 0,
  attempt         INTEGER NOT NULL DEFAULT 1,
  notes           TEXT NOT NULL DEFAULT '',
  created_at      TEXT,
  updated_at      TEXT,
  UNIQUE (batch_id, oeis_name, formula_hash)
);
"""


def ensure_schema(conn: sqlite3.Connection) -> None:
    conn.executescript(MIGRATION_SQL)
    conn.commit()


def create_batch(conn: sqlite3.Connection, names: list[str]) -> int:
    cur = conn.execute(
        """INSERT INTO formalization_batch
             (language, model, status, oeis_names, max_attempts,
              created_at, updated_at)
           VALUES (?, 'linearrecurrence-wolfram', 'BATCH_RUNNING', ?, 1,
                   datetime('now'), datetime('now'))""",
        ("mathematica", json.dumps(sorted(set(names)))),
    )
    conn.commit()
    return int(cur.lastrowid)


def mark_verified(
    conn: sqlite3.Connection,
    batch_id: int,
    f: LRFormula,
    lean_file: str,
    check_file: str,
    verified_upto: int,
    arg_kind: str,
) -> None:
    conn.execute(
        """INSERT INTO formalization_item
             (batch_id, oeis_name, language, source_hash, formula_hash,
              original_text, computable, arg_kind, lean_file, check_file,
              depends_on, status, verified_upto, attempt, notes,
              created_at, updated_at)
           VALUES (?, ?, 'mathematica', ?, ?, ?, 1, ?, ?, ?, '[]',
                   'STATUS_VERIFIED', ?, 1, ?,
                   datetime('now'), datetime('now'))
           ON CONFLICT(batch_id, oeis_name, formula_hash)
           DO UPDATE SET status='STATUS_VERIFIED',
                         verified_upto=excluded.verified_upto,
                         lean_file=excluded.lean_file,
                         updated_at=datetime('now')""",
        (
            batch_id, f.oeis_name, f.source_hash, f.formula_hash,
            f.original_text, arg_kind, lean_file, check_file,
            verified_upto,
            (f"author={f.author}; date={f.date}" if f.author or f.date else ""),
        ),
    )
    # Also update the formula table, if the formula_hash matches an entry.
    conn.execute(
        """UPDATE formula SET status='STATUS_VERIFIED',
                              formalized_formula=?
           WHERE oeis_name=? AND hash=?""",
        (f.original_text, f.oeis_name, f.formula_hash),
    )
    conn.commit()


def mark_failed(
    conn: sqlite3.Connection,
    batch_id: int,
    f: LRFormula,
    lean_file: str,
    diags: list[str],
    failure_kind: str,
) -> None:
    conn.execute(
        """INSERT INTO formalization_item
             (batch_id, oeis_name, language, source_hash, formula_hash,
              original_text, computable, lean_file, depends_on, status,
              failure_kind, compiler_output, attempt, created_at, updated_at)
           VALUES (?, ?, 'mathematica', ?, ?, ?, 1, ?, '[]', ?, ?, ?, 1,
                   datetime('now'), datetime('now'))
           ON CONFLICT(batch_id, oeis_name, formula_hash)
           DO UPDATE SET status=excluded.status,
                         failure_kind=excluded.failure_kind,
                         compiler_output=excluded.compiler_output,
                         updated_at=datetime('now')""",
        (
            batch_id, f.oeis_name, f.source_hash, f.formula_hash,
            f.original_text, lean_file, failure_kind,
            "\n".join(diags)[:20000],
        ),
    )
    conn.commit()


# ---------------------------------------------------------------------------
# Main orchestration
# ---------------------------------------------------------------------------

def arg_kind_for_offset(offset: int) -> str:
    if offset == 0:
        return "Nat"
    if offset == 1:
        return "PNat"
    if offset > 1:
        return "NatSub"
    return "IntSub"


def defs_exists(loeis_dir: Path, name: str) -> bool:
    return (loeis_dir / name[:4] / name / "Defs.lean").is_file()


def data_exists(loeis_dir: Path, name: str) -> bool:
    return (loeis_dir / name[:4] / name / "Data.lean").is_file()


def run(args: argparse.Namespace) -> int:
    db_path: Path = args.db
    loeis_dir: Path = args.out
    check_dir: Path = args.check_dir
    seq_dir: Path = args.seq_dir
    template = TEMPLATE_PATH.read_text(encoding="utf-8")

    conn = connect_db(db_path)

    # 1. Collect formulas.
    formulas: list[LRFormula] = []
    if conn is not None:
        print("Scanning mathematica program blocks from database ...", file=sys.stderr)
        formulas = scan_from_db(conn, args.bucket, args.seq)
        if not formulas and seq_dir.is_dir():
            print("No DB hits; falling back to .seq file scan ...", file=sys.stderr)
            formulas = scan_from_seq_files(seq_dir, args.bucket, args.seq)
            enrich_from_db(formulas, conn)
    elif seq_dir.is_dir():
        print("Database not available; scanning .seq files ...", file=sys.stderr)
        formulas = scan_from_seq_files(seq_dir, args.bucket, args.seq)
    else:
        print(
            f"error: neither {db_path} nor {seq_dir} is available", file=sys.stderr
        )
        return 1

    # Deduplicate by (oeis_name, formula_hash).
    seen: set[tuple[str, str]] = set()
    unique: list[LRFormula] = []
    for f in formulas:
        key = (f.oeis_name, f.formula_hash)
        if key in seen:
            continue
        seen.add(key)
        unique.append(f)
    formulas = unique

    if args.limit:
        formulas = formulas[: args.limit]

    # 2. Filter to sequences that have Lean skeletons.
    missing: list[LRFormula] = []
    eligible: list[LRFormula] = []
    for f in formulas:
        if not f.terms:
            missing.append(f)
            continue
        if not defs_exists(loeis_dir, f.oeis_name):
            missing.append(f)
            continue
        eligible.append(f)

    print(
        f"Found {len(formulas)} LinearRecurrence call(s); "
        f"{len(eligible)} eligible for formalization, "
        f"{len(missing)} skipped (no Defs.lean / no terms).",
        file=sys.stderr,
    )

    if args.dry_run:
        for f in eligible:
            print(f"\n=== {f.oeis_name}  Equiv_{f.formula_hash} ===")
            print(f"  offset={f.offset}  order={len(f.coeffs)}")
            print(f"  coeffs={f.coeffs}")
            print(f"  init={f.init}")
            if f.author or f.date:
                print(f"  author={f.author!r}  date={f.date!r}")
            print(f"  source: {f.original_text}")
        return 0

    if not eligible:
        print("Nothing to formalize.", file=sys.stderr)
        return 0

    # 3. Ensure DB schema and create a batch.
    if conn is not None:
        ensure_schema(conn)
        batch_id = create_batch(conn, [f.oeis_name for f in eligible])
    else:
        batch_id = 0

    batch_check_dir = check_dir / "LinearRecurrence" / f"B{batch_id}"
    batch_check_dir.mkdir(parents=True, exist_ok=True)

    # 4. Write Equiv + check files.
    targets: list[str] = []
    equiv_paths: dict[str, Path] = {}
    check_paths: dict[str, Path] = {}
    for f in eligible:
        key = f"{f.oeis_name}:{f.formula_hash}"
        equiv_name = f"Equiv_{f.formula_hash}"
        equiv_path = loeis_dir / _bucket(f.oeis_name) / f.oeis_name / f"{equiv_name}.lean"
        equiv_path.parent.mkdir(parents=True, exist_ok=True)
        equiv_path.write_text(render_equiv(f, template), encoding="utf-8")
        equiv_paths[key] = equiv_path

        check_path = batch_check_dir / f"{f.oeis_name}_{f.formula_hash}.lean"
        check_path.write_text(
            render_check(f, batch_id, args.terms), encoding="utf-8"
        )
        check_paths[key] = check_path
        targets.append(
            f"{CHECK_LIB}.LinearRecurrence.B{batch_id}."
            f"{f.oeis_name}_{f.formula_hash}"
        )

    # 5. Build.
    print(f"Building {len(targets)} check module(s) ...", file=sys.stderr)
    build = lake_build(targets, args.timeout)

    # 6. Classify and persist.
    verified = 0
    failed = 0

    def _rel(p: Path) -> str:
        """Path relative to REPO_ROOT when possible, otherwise absolute."""
        try:
            return str(p.relative_to(REPO_ROOT))
        except ValueError:
            return str(p)

    for f in eligible:
        key = f"{f.oeis_name}:{f.formula_hash}"
        ep = equiv_paths[key]
        cp = check_paths[key]
        diags = build.diagnostics_for(str(ep), str(cp), _rel(ep), _rel(cp))
        if not diags and build.timed_out:
            diags = ["build timed out; the definition is probably too slow to evaluate"]
        rel_ep = _rel(ep)
        rel_cp = _rel(cp)
        if diags:
            failed += 1
            kind = (
                "STATUS_EVAL_MISMATCH"
                if any("OEIS_CHECK_FAIL" in d for d in diags)
                else "STATUS_COMPILE_ERROR"
            )
            print(f"FAIL {f.oeis_name} Equiv_{f.formula_hash}: {kind}",
                  file=sys.stderr)
            if conn is not None:
                mark_failed(conn, batch_id, f, rel_ep, diags, kind)
            # Remove the Equiv file on failure so the tree stays clean.
            ep.unlink(missing_ok=True)
        else:
            verified += 1
            print(f"OK   {f.oeis_name} Equiv_{f.formula_hash}", file=sys.stderr)
            checked_upto = min(args.terms, len(f.terms))
            if conn is not None:
                mark_verified(
                    conn, batch_id, f, rel_ep, rel_cp,
                    checked_upto, arg_kind_for_offset(f.offset),
                )

    # 7. Update batch status.
    if conn is not None:
        status = "BATCH_OK" if failed == 0 else ("BATCH_PARTIAL" if verified else "BATCH_FAILED")
        conn.execute(
            "UPDATE formalization_batch SET status=?, attempts=1, "
            "updated_at=datetime('now') WHERE id=?",
            (status, batch_id),
        )
        conn.commit()

    # 8. Clean up check files.
    if not args.keep_check_files:
        shutil.rmtree(batch_check_dir, ignore_errors=True)

    print(
        f"Done. verified={verified} failed={failed} batch_id={batch_id}",
        file=sys.stderr,
    )
    return 0 if failed == 0 else 1


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="linearrecurrence-wolfram",
        description="Formalize Mathematica LinearRecurrence %t lines into Lean.",
    )
    p.add_argument("--db", type=Path, default=DEFAULT_DB,
                   help="path to Metadata/oeis.db")
    p.add_argument("--seq-dir", type=Path, default=DEFAULT_SEQ_DIR,
                   help="directory containing A000/A000001.seq etc.")
    p.add_argument("--out", type=Path, default=DEFAULT_LOEIS,
                   help="LOEIS output directory")
    p.add_argument("--check-dir", type=Path, default=DEFAULT_CHECK,
                   help="Check directory for temporary validation modules")
    p.add_argument("--bucket", action="append", default=None,
                   help="restrict to a bucket, e.g. A000")
    p.add_argument("--seq", action="append", default=None,
                   help="restrict to an A-number")
    p.add_argument("--terms", type=int, default=20,
                   help="number of OEIS terms to validate against")
    p.add_argument("--timeout", type=int, default=900,
                   help="lake build timeout in seconds")
    p.add_argument("--limit", type=int, default=0,
                   help="process at most N formulas (0 = no limit)")
    p.add_argument("--dry-run", action="store_true",
                   help="parse and print what would be formalized, without building")
    p.add_argument("--keep-check-files", action="store_true",
                   help="do not delete the generated Check modules")
    return p


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    return run(args)


if __name__ == "__main__":
    raise SystemExit(main())
