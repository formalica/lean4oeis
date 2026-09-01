# SPEC — index

Design specification of the OEIS formalization pipeline (Lean 4 + Mathlib).

| Document | Covers |
| --- | --- |
| [Architecture.md](Architecture.md) | Pipeline overview: ingest → database → skeleton generation → formalization (templates / formula parser) → verification → build |
| [Database.md](Database.md) | `Metadata/oeis.db` SQLite schema: the `sequence` and `formula` tables, columns, statuses, refresh semantics |
| [Ingest.md](Ingest.md) | `oeis-ingest`: parsing OEIS `.seq` internal-format files into the database |
| [Generator.md](Generator.md) | `oeis-gen`: `Defs.lean` / `Data.lean` skeleton generation from the database |
| [FormulaParser.md](FormulaParser.md) | `FormulaParser` library: plain-text formula → AST → ranked Lean terms |
| [Templates.md](Templates.md) | `oeis-template` runner and per-family templates |
| [OEISLib.md](OEISLib.md) | Per-sequence file shape: `Defs.lean`, `Data.lean`, `Equiv_<hash>.lean`, `Basic_<hash>.lean` for scalar, table and decimal sequences |
| [Verification.md](Verification.md) | How formulas are checked against the known data; statuses |
| [BuildAndCache.md](BuildAndCache.md) | Lake targets, CI workflows, the `.lake/build` cache tool |
| [Diff.md](Diff.md) | What `origin/main` contains that this branch does not (LLM-agent pipeline, `Check/`, program-block ingest, new tables) |

Older design notes in the repo root: `SPEC.md` (original requirements),
`OEIS.md` (file-shape notes), `TEMPLATES.md` (template authoring guide).
These SPEC documents are the precise, current reference; where they and the
root notes disagree, the SPEC wins.
