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

Step 1 of SPEC.md (metadata tables) is **done**. Nothing else is implemented yet.

The ingest executable walks `oeisdata/seq`, parses every `.seq` file, and populates a SQLite
database at `Metadata/oeis.db` (git-ignored, ~360 MB).

### Files

| Path | Purpose |
| --- | --- |
| [Scripts/OeisIngest.lean](Scripts/OeisIngest.lean) | `main`, CLI args, directory walk, transaction batching |
| [Scripts/OeisIngest/Parse.lean](Scripts/OeisIngest/Parse.lean) | `.seq` record parser, `Entry` struct, `formulaHash` |
| [Scripts/OeisIngest/Db.lean](Scripts/OeisIngest/Db.lean) | schema DDL, prepared upsert statements |
| [Scripts/OeisIngest/Json.lean](Scripts/OeisIngest/Json.lean) | minimal JSON array/string emitter, hex encoder |
| [lakefile.toml](lakefile.toml) | `Scripts` lean_lib + `oeis-ingest` lean_exe |

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
```

`--limit N` truncates to the first N `.seq` files — use it for fast iteration.
Full run: ~2m25s, 396,006 sequences, 527,877 formula rows.

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
4. Lean file generation into `Axxx/Axxxxxx/`.

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

## RULE 0 reminder

Repeating [RULE 0](#rule-0--keep-this-file-up-to-date-mandatory) as promised:

> **After every user prompt you act on, update this file** — append to the progress log, refresh
> the current state / schema / commands sections, and re-prioritize the open items. Do this
> before you end your turn, every time, without being asked.
