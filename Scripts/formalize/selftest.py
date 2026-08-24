"""Offline check of the Lean templates: renders a few hand-written translations and builds
them, without calling any model. Run with `PYTHONPATH=Scripts .venv/bin/python -m formalize.selftest`."""

from __future__ import annotations

import json
import sys

from . import db as dbm
from . import lean
from .config import Config
from .models import BatchResult, FormalizedProgram
from .pipeline import _classify, _cleanup, _validate, _write_files, collect_dep_infos, seq_info_from_row
from .render import SeqInfo

CASES = [
    ("A000045", "A000045 := proc(n)", "combinat[fibonacci](n); end;", "Nat", True,
     "def formula : Nat → Nat\n"
     "  | 0 => 0\n"
     "  | 1 => 1\n"
     "  | n + 2 => formula n + formula (n + 1)"),
    ("A001006", "add(binomial(n,2*k)", "k=0..floor(n/2)) ;", "Nat", True,
     "def formula : Nat → Nat := fun n =>\n"
     "  ∑ k ∈ Finset.range (n / 2 + 1), Nat.choose n (2 * k) * A000108.fn k"),
    ("A000040", "A000040 := n->ith", "n->ithprime(n);", "PNat", True,
     "def formula : PNat → Nat := fun n => n + 1"),
]


def main() -> int:
    cfg = Config.from_env()
    conn = dbm.connect(cfg.db_path)
    names = [c[0] for c in CASES]
    rows = dbm.select_programs(conn, "maple", limit=200, seqs=names, include_attempted=True)
    by_name: dict[str, dbm.ProgramRow] = {}
    for row in rows:
        by_name.setdefault(row.oeis_name, row)
    for name, start, end, _, _, _ in CASES:
        if name not in by_name:
            print(f"no maple block for {name}", file=sys.stderr)
            return 1
        for marker in (start, end):
            if marker not in by_name[name].text:
                print(f"marker {marker!r} not present in {name} block:\n"
                      f"{by_name[name].text}", file=sys.stderr)
                return 1

    picked = [by_name[n] for n in names]
    seq_infos = {r.oeis_name: SeqInfo(r.oeis_name, r.title, r.offset, r.terms) for r in picked}
    dep_seqs = collect_dep_infos(conn, cfg, picked)
    result = BatchResult(items=[
        FormalizedProgram(oeis_name=n, start_marker=s, end_marker=e, lean_code=c,
                          arg_kind=k, computable=comp)
        for n, s, e, k, comp, c in CASES
    ])
    accepted, rejected, found = _validate(result, picked, seq_infos, dep_seqs)
    for r in rejected:
        print("REJECTED:", r.render())
    for gap in found:
        print(f"{'trivial gap' if gap.trivial else 'UNFORMALIZED'} {gap.oeis_name} "
              f"[{gap.span.start}:{gap.span.end}]: {gap.text[:120]!r}")
    targets = _write_files(cfg, 0, accepted, dep_seqs)
    print("targets:", targets)
    build = lean.build(targets, cfg.build_timeout)
    failed, passed = _classify(cfg, accepted, build)
    print("build ok:", build.ok)
    for item in passed:
        print("PASS", item.key)
    for item, kind, diags in failed:
        print("FAIL", item.key, kind)
        print("   ", "\n    ".join(diags)[:1500])
        print("   points:", json.dumps(lean.parse_failure_points(diags, item.seq.offset)))
    # These are fixtures, not real formalizations: never leave them in the tree.
    _cleanup(cfg, 0, accepted)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
