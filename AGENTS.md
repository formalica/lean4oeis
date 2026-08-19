# AGENTS.md

Instructions and living project log for AI agents working in this repository.
(VS Code / Copilot automatically loads `AGENTS.md`, so this is the file to keep current.)

## RULE 0 — Keep this file up to date (MANDATORY)

**After every user prompt you act on, you MUST update this file before finishing your turn.**

- Append what you did to [Progress log](#progress-log) with the date.
- Update [Current state](#current-state), [Database schema](#database-schema), and
  [Commands](#commands) whenever they change.
- Update [Open items / next steps](#open-items--next-steps): remove what is done, add what
  the new work revealed.
- Record decisions the user made (naming, formats, tool choices) under [Decisions](#decisions)
  so they are not re-litigated.
- Keep it short. This is a working index, not documentation. Delete stale lines instead of
  letting the file grow.

This rule is repeated at the [bottom of the file](#rule-0-reminder) on purpose. Do not skip it.

## Project

Formalize OEIS sequences in Lean 4 + Mathlib. The end goal (see [SPEC.md](SPEC.md) and
[OEIS.md](OEIS.md)) is to generate, per sequence `Axxxxxx`, a directory `Axxx/Axxxxxx/` with:

- `Defs.lean` — main definition (`Axxxxxx`, `argType`, `retType`, `offset`, `fn`, `fz`, `prop`,
  coherence theorems)
- `Data.lean` — known terms + `data_eq` / `data_eq_fn` / `data_eq_fz`
- `Equiv_<hash>.lean` — alternative definitions + equivalence to the main definition
- `Basic_<hash>.lean` — properties that do not fully determine the sequence

Raw OEIS data lives in `oeisdata/seq/A<bucket>/A<number>.seq` (396,006 files, git-ignored,
official OEIS "internal format").

## Current state

Step 1 of SPEC.md (metadata tables) is **done**, and the `Defs.lean` / `Data.lean` skeleton
generator is **done**. Formula parsing / real definitions are not started.

The ingest executable walks `oeisdata/seq`, parses every `.seq` file, and populates a SQLite
database at `Metadata/oeis.db` (git-ignored, ~360 MB). The generator reads that DB and writes
`LOEIS/<bucket>/<name>/{Defs,Data}.lean` where every declaration is `sorry`.

### Generated skeleton shape

`argType` from the OEIS offset:

| offset | `argType` | `fn` generated? |
| --- | --- | --- |
| `0` | `Nat` | yes |
| `1` | `PNat` | yes |
| `k ≥ 2` | `{n : Nat // k ≤ n}` | yes |
| `k < 0` | `{n : Int // k ≤ n}` | no (SPEC: skip `fn` for Int-based argTypes) |

`retType` is `Int` if any known term is negative, else `Nat`.

`tabl` / `tabf` sequences (31,428 of them) are two-argument in reality; for now they get a
flattened API and every name gains a prefix: `flat`, `flatArgType`, `flatRetType`, `flatOffset`,
`flatFn`, `flatFz`, `flatProp`, `flatData`, and `flat_prop_correct`, `flat_fn_eq`, `flat_fz_eq`,
`flat_fn_eq_fz`, `flat_data_eq`, `flat_data_eq_fn`, `flat_data_eq_fz`. Non-flat sequences keep
the main definition at top level (`def A000001 : A000001.argType → A000001.retType`); flat ones
put it inside the namespace as `A000012.flat`.

`data` holds every term OEIS knows, indexed from `offset`, so `a(n) = data[n - offset]`.

Aggregators are rebuilt from the filesystem on every run: `LOEIS/<bucket>/{Defs,Data}.lean`
import each sequence, and `LOEIS/{Defs,Data}.lean` import each bucket.

### Files

| Path | Purpose |
| --- | --- |
| [Scripts/OeisIngest.lean](Scripts/OeisIngest.lean) | `main`, CLI args, directory walk, transaction batching |
| [Scripts/OeisIngest/Parse.lean](Scripts/OeisIngest/Parse.lean) | `.seq` record parser, `Entry` struct, `formulaHash` |
| [Scripts/OeisIngest/Db.lean](Scripts/OeisIngest/Db.lean) | schema DDL, prepared upsert statements |
| [Scripts/OeisIngest/Json.lean](Scripts/OeisIngest/Json.lean) | minimal JSON array/string emitter, hex encoder |
| [Scripts/OeisGen.lean](Scripts/OeisGen.lean) | `main`, CLI args, DB query, file writing, aggregators |
| [Scripts/OeisGen/Render.lean](Scripts/OeisGen/Render.lean) | `Defs.lean` / `Data.lean` text templates, `ArgKind`, `Names` |
| [lakefile.toml](lakefile.toml) | `Scripts` lean_lib + `oeis-ingest` / `oeis-gen` lean_exe, `LOEIS.+` glob |

### Parsed OEIS record tags

`%S`/`%T`/`%U` terms · `%N` title · `%O` offset · `%K` keywords · `%F` formulas.
Everything else (`%C`, `%D`, `%H`, `%e`, `%p`, `%t`, `%o`, `%Y`, `%A`, `%E`, `%I`) is ignored
for now.

## Database schema

`Metadata/oeis.db`. Columns that later stages fill in are created empty / `STATUS_UNKNOWN`;
re-running the ingest refreshes only OEIS-derived columns and preserves them.

### `sequence`

| Column | Notes |
| --- | --- |
| `name` | `Axxxxxx`, PRIMARY KEY |
| `title` | `%N` |
| `"offset"` | first component of `%O` (must be quoted — SQL keyword) |
| `offset_first_big` | second component of `%O` |
| `keywords` | JSON array of strings |
| `data` | JSON array of bare integer numerals (arbitrary precision) |
| `data_count` | number of terms |
| `main_definition_hash` | *filled later* — NULL |
| `formalized_formula_hashes` | *filled later* — `[]` |
| `unformalized_formula_hashes` | JSON array of `%F` hashes |
| `all_unformalized_formulas_text` | JSON array of raw `%F` lines |
| `status` | `STATUS_UNKNOWN` |
| `source_file`, `updated_at` | provenance |

### `formula`

PRIMARY KEY `(oeis_name, hash)`; indexes on `hash` and `status`.

| Column | Notes |
| --- | --- |
| `hash` | 16 hex chars of `String.hash` of the formula text |
| `oeis_name`, `human_written_formula` | from `%F` |
| `formalized_formula`, `type` | *filled later* — `''` |
| `status` | `STATUS_UNKNOWN` → `STATUS_PROVED` / `STATUS_VERIFIED` / `STATUS_SORRY` |
| `verification_values`, `disproved_values`, `additional_conditions` | *filled later* — `[]` |
| `source_tag`, `line_index` | `'F'` and position within the sequence |

## Commands

```bash
lake build oeis-ingest
lake exe oeis-ingest [--seq-dir oeisdata/seq] [--db Metadata/oeis.db] [--limit N]

lake build oeis-gen
lake exe oeis-gen [--db Metadata/oeis.db] [--out LOEIS] [--all] [--bucket A000]... [--seq A000001]... [--force]
```

`--limit N` truncates to the first N `.seq` files — use it for fast iteration.
Full ingest run: ~2m25s, 396,006 sequences, 527,877 formula rows.

`oeis-gen` never overwrites an existing file unless `--force` is passed, so later stages that
replace `sorry` with real definitions are safe from regeneration.

No `sqlite3` CLI on this machine; inspect the DB with `python3 -c "import sqlite3; ..."`.

## Decisions

- **Scope**: ingest all ~396k sequences, no keyword filtering.
- **DB path**: `Metadata/oeis.db`.
- **Hashing**: `String.hash` (fast), rendered as 16 lowercase hex chars. SHA-256 rejected as
  too slow.
- **Lists**: always stored as JSON serialized to a `TEXT` column.
- **Re-run semantics**: upsert. OEIS-derived columns refreshed, formalization columns
  untouched. Verified by test.
- **`%C` (comments) are never ingested** — not stored, not treated as formula candidates.
- **Multi-line `%F` blocks stay split one-row-per-line for now.** Lines that carry no formula
  (e.g. `"From _Mitch Harris_, ... (Start)"`, `"(End)"`) are expected to just fail to parse
  later and be skipped — no special-casing needed at ingest time.
- **Subtype bounds use `offset ≤ n`**, consistent with `PNat` for offset 1 and `Nat` for offset 0.
- **Generated files import `Mathlib.Tactic` + `Mathlib.Data.PNat.Defs`.**
- **Linter options live in `lakefile.toml`, never in generated files** —
  `weak.linter.unusedVariables = false` and `weak.linter.style.longLine = false`, because the
  skeletons have unused binders (proofs are `sorry`) and very long term lists by construction.

## Lean 4.34 gotchas (this toolchain)

- `String.drop`/`take`/`takeWhile`/`dropWhile` return `String.Slice`, not `String`.
  Convert with `.toString`.
- `String.trim`/`trimLeft`/`trimRight` are deprecated; use `trimAscii` / `trimAsciiStart` /
  `trimAsciiEnd` (they return `Slice`).
- `String.mk` is deprecated; use `String.ofList`.
- `String.Pos` is now dependent (`s.Pos`), so `⟨0⟩` literals and `posOf` are awkward — prefer
  `splitOn` / list-based parsing.
- `leansqlite` is built with `experimental.module`; `SQLite.open` must be written
  `SQLite.«open»`.
- A `lean_exe` root outside any `lean_lib` glob will not get its imports built. The `Scripts`
  `lean_lib` in `lakefile.toml` exists for exactly this reason.
- The Lean language server can report stale `unknown module prefix` errors after `lakefile.toml`
  changes; restart the Lean server, `lake build` is the source of truth.

## Open items / next steps

1. Multi-line `%F` blocks (`... (Start)` / `... (End)`) are currently split into one row per
   line. Group them before treating each line as a standalone formula.
2. Stage-2 of SPEC.md: strip formulas from `all_unformalized_formulas_text` as they get
   formalized, so the remainder converges on pure "properties".
3. Formula AST + parser (`generate_lseq`), type inference, interpretation search
   (`Nat` → `Int` → `Real`, main def → `fn` → `fz`), validated against `sequence.data`.
4. Fill the `sorry`s in `Defs.lean` from the parsed `%N` title, then `Equiv_<hash>.lean` /
   `Basic_<hash>.lean` from the `%F` formulas.
5. `tabl`/`tabf` sequences currently get the flattened one-argument API only; the real
   two-argument version is deferred.
6. Build cost: `import Mathlib.Tactic` in every generated file makes a full 396k-sequence build
   impractical. Revisit if the A000 bucket build turns out too slow.

## Progress log

- **2026-08-18** — Implemented SPEC.md step 1: `oeis-ingest` executable, `.seq` parser, JSON
  helpers, `sequence` + `formula` tables. Full ingest run: 396,006 sequences / 527,877
  formulas. Verified signed terms (`A001057`), 54-digit bignums (`A000178`), and upsert
  idempotency (formalization columns preserved, no duplicate rows). Added `Metadata/*.db` to
  `.gitignore`.
- **2026-08-18** — Created this file and adopted RULE 0 (agent updates `AGENTS.md` after every
  prompt).
- **2026-08-18** — Printed full `sequence`/`formula` rows for `A000001` to inspect real data.
  Confirmed with user: `%C` lines stay excluded (already the case), and standalone `%F`
  continuation lines like `(Start)`/`(End)` are fine to keep as their own formula rows — the
  later formalization parser is expected to just skip them silently.
- **2026-08-19** — Added `oeis-gen`: renders `Defs.lean` + `Data.lean` skeletons (all `sorry`)
  per sequence, plus bucket and root aggregators. Verified all four `argType` shapes and the
  flat/`tabl` variant compile: `A000001` (Nat), `A000027` (PNat + tabl), `A000063` (offset 5
  subtype), `A000297` (offset -1, Int subtype, no `fn`), `A000023`/`A000036` (Int retType).
  Moved the `unusedVariables` / `longLine` linter options out of generated files into
  `lakefile.toml`.
- **2026-08-20** — Rewrote README.md: elan/toolchain setup, `lake exe cache get`, oeisdata
  acquisition pointer, then the three-step ingest → gen → build pipeline with common flags.

## RULE 0 reminder

Repeating [RULE 0](#rule-0--keep-this-file-up-to-date-mandatory) as promised:

> **After every user prompt you act on, update this file** — append to the progress log, refresh
> the current state / schema / commands sections, and re-prioritize the open items. Do this
> before you end your turn, every time, without being asked.
