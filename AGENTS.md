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

Step 1 of SPEC.md (metadata tables) is **done**, the `Defs.lean` / `Data.lean` skeleton
generator is **done**, the stage-1 formula parser (`FormulaParser/`) is **done**, and two
**templates** are **fully applied**: `walkN3` (~3254 Bostan–Kauers octant-walk sequences) and `coxeter`
(~2302 complete-graph Coxeter group sequences, g∈[3,50] r∈[3,50]): all have a real computable
`Defs.lean` plus an `Equiv_<hash>.lean` with a proved `formula_eq`, and their `%F`/`%t`/`%o`
snippets are marked in `oeis.db` (2290 with ≥1 Equiv, 12 with only `Defs.lean` — atypical G.f. left to generic parser).

The ingest executable walks `oeisdata/seq`, parses every `.seq` file, and populates a SQLite
database at `Metadata/oeis.db` (git-ignored, ~360 MB). The generator reads that DB and writes
`LOEIS/<bucket>/<name>/{Defs,Data}.lean` where every declaration is `sorry`.
Templates (`lake exe oeis-template`) then *overwrite* selected sequences' `Defs.lean` with
real definitions and add `Equiv_<hash>.lean`; `Data.lean` skeletons are untouched so far.

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
| [OEISLib/Walk3.lean](OEISLib/Walk3.lean) | generic 3D octant-walk library: high-level `count`, low-level `aux`/`countDp` (Wolfram transcription), `countDp_eq_count` |
| [Scripts/OeisIngest.lean](Scripts/OeisIngest.lean) | `main`, CLI args, directory walk, transaction batching |
| [Scripts/OeisIngest/Parse.lean](Scripts/OeisIngest/Parse.lean) | `.seq` record parser, `Entry` struct, `formulaHash` |
| [Scripts/OeisIngest/Db.lean](Scripts/OeisIngest/Db.lean) | schema DDL, prepared upsert statements |
| [Scripts/OeisIngest/Json.lean](Scripts/OeisIngest/Json.lean) | minimal JSON array/string emitter, hex encoder |
| [Scripts/OeisGen.lean](Scripts/OeisGen.lean) | `main`, CLI args, DB query, file writing, aggregators |
| [Scripts/OeisGen/Render.lean](Scripts/OeisGen/Render.lean) | `Defs.lean` / `Data.lean` text templates, `ArgKind`, `Names` |
| [Scripts/OeisTemplate.lean](Scripts/OeisTemplate.lean) | **template runner** exe: CLI, selection, `.seq` loading, dispatch, reporting |
| [Scripts/OeisTemplate/Registry.lean](Scripts/OeisTemplate/Registry.lean) | `Context` / `SeqInput` / `Outcome` / `Template` types, `markFormalized` DB helper |
| [Scripts/Templates/Registry.lean](Scripts/Templates/Registry.lean) | list of registered templates + lookup |
| [Scripts/Templates/WalkN3.lean](Scripts/Templates/WalkN3.lean) | `walkN3` template: title/%t parsing, recognizer, DP verifier, renderers |
| [OEISLib/Coxeter.lean](OEISLib/Coxeter.lean) | generic Coxeter growth library: `coxSeq` via power-series division (`numCoeffs`/`denCoeffs`), `coeffsUpTo`, `coeffsUpTo_getElem` |
| [Scripts/Templates/Coxeter.lean](Scripts/Templates/Coxeter.lean) | `coxeter` template: title `(g,r)` parsing, `%F`/`%t`/`%o` recognizers (G.f. rational+factored, recurrence, `coxG`, `CoefficientList[Series]`, PARI `Vec`, Magma `PowerSeriesRing`), verifier, renderers |
| [Scripts/OeisCache.lean](Scripts/OeisCache.lean) | `prune` / `stat` / `put` / `get` for `.lake/build` artifacts |
| [Scripts/OeisParseReport.lean](Scripts/OeisParseReport.lean) | standalone report: parse every raw `%F` line of the first *N* sequences as `Nat → Int`, time it, data-validate (reports → /tmp; run via `lake env lean --load-dynlib=...libleansqlite.so --load-dynlib=...leansqlite_SQLite_FFI.so Scripts/OeisParseReport.lean`; currently `LIMIT 100` → 1153 lines, see `/tmp/opencode/formula_parse_report_1000*`) |
| [Scripts/name_templates.py](Scripts/name_templates.py) | standalone python3 miner: groups `%N` titles into constant-parameter templates → writes [Scripts/templates.txt](Scripts/templates.txt) |
| [Scripts/templates.txt](Scripts/templates.txt) | generated: corpus-wide name-template inventory, 704 templates ≥25 members covering 66,238 sequences, frequency-sorted markdown table |
| [TEMPLATES.md](TEMPLATES.md) | how to create a new template (only user-stated requirements, with walkN3/coxeter as examples) |
| [lakefile.toml](lakefile.toml) | libs `LOEIS` / `OEISLib` / `FormulaParser` / `Scripts`, exes `oeis-ingest` / `oeis-gen` / `oeis-cache` / `oeis-template` |

### Parsed OEIS record tags

`%S`/`%T`/`%U` terms · `%N` title · `%O` offset · `%K` keywords · `%F` formulas.
Everything else (`%C`, `%D`, `%H`, `%e`, `%p`, `%t`, `%o`, `%Y`, `%A`, `%E`, `%I`) is ignored
for now, except templates read `%t`/`%o` snippets directly from the raw `.seq` files.

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
| `oeis_name`, `human_written_formula` | from `%F`, or the matched `%t` snippet for Wolfram rows |
| `formalized_formula`, `type` | templates store the generated `Equiv_<hash>.lean` body here, `type='computable_definition'` |
| `status` | `STATUS_UNKNOWN` → `STATUS_PROVED` / `STATUS_VERIFIED` / `STATUS_SORRY`; walkN3/coxeter write `STATUS_VERIFIED` (values data-checked; `formula_eq` itself is fully proved) |
| `verification_values`, `disproved_values`, `additional_conditions` | walkN3 fills `verification_values` with `"n:value"` strings |
| `source_tag`, `line_index` | `'F'` for formula lines, `'T'` for `%t` Wolfram rows, `'O'` for `%o`; position within the sequence |

Template rows survive re-ingest: the ingest upsert never deletes unknown rows.

## Commands

```bash
lake build oeis-ingest
lake exe oeis-ingest [--seq-dir oeisdata/seq] [--db Metadata/oeis.db] [--limit N]

lake build oeis-gen
lake exe oeis-gen [--db Metadata/oeis.db] [--out LOEIS] [--all] [--bucket A000]... [--seq A000001]... [--force]

lake build oeis-cache
lake exe oeis-cache <prune|stat|put|get> [--archive PATH] [--manifest PATH] [--build-dir PATH] [--level N] [--force]

# template runner: mandatory = template name + selection; everything else defaults
lake build oeis-template
lake exe oeis-template <template> (--all | [--bucket A147]... [--seq A147999]...)
lake exe oeis-template walkN3 --seq A147999 --seq A151162 --force   # first application needs --force (sorry skeletons exist)
lake exe oeis-template walkN3 --bucket A148 --dry-run               # parse+verify only, no writes
lake exe oeis-template walkN3 --all --table-max=20 --check-cap=8    # template-private params pass through
lake exe oeis-template coxeter --seq A162740 --dry-run --force     # Coxeter: g=4 r=3
lake exe oeis-template coxeter --all --check-cap=12 --force        # full 2302

# %N name-template miner (plain python3, no lake): regenerates Scripts/templates.txt
python3 Scripts/name_templates.py [--seq-dir oeisdata/seq] [--out Scripts/templates.txt] [--min-count 25]
```

`--limit N` truncates to the first N `.seq` files — use it for fast iteration.
Full ingest run: ~2m25s, 396,006 sequences, 527,877 formula rows.

`oeis-gen` never overwrites an existing file unless `--force` is passed, so later stages that
replace `sorry` with real definitions are safe from regeneration.

No `sqlite3` CLI on this machine; inspect the DB with `python3 -c "import sqlite3; ..."`.

## Coxeter notes

`OEISLib.Coxeter.coxSeq` is defined by power-series division `G = num/den` with
`num = 1+2t+…+2t^{r-1}+t^r`, `den = 1-(g-2)(t+…+t^{r-1})+C(g-1,2)t^r`. Recurrence
`a(n) = (g-2)Σ_{k=1}^{r-1} a(n-k) -C·a(n-r)` is implicit in the division. `g=3` sequences
have atypical printed G.f. (` -2 t^k + t^{k+1}` alternating, degree r-1) but satisfy the same
division — those 12 have only `Defs.lean` (no `Equiv`) until a `g=3`-specific recognizer is added.
`Equiv` bundles all matched `%F`/`%t`/`%o` flavors into one file (`hash = formulaHash(concat matched)`);
defines `formula : List Nat` (not `programList`/custom names) and `formula_eq` uses `coeffsUpTo_getElem` bridge (not `rfl` via `List.range`).

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
- **Hosting moves to Hugging Face**: `https://huggingface.co/datasets/formalica/lean4oeis`.
  GitHub is dropped (CI in `workflows/` is lost). All 792k `LOEIS/**.lean` files are committed
  raw, despite HF recommending <100k files per repo.
- **`oeisdata` is NOT a submodule** — it stays git-ignored and users clone it themselves,
  shallow + sparse (`seq/` only), from `https://github.com/oeis/oeisdata`.
- **`Metadata/oeis.db` is committed via Git LFS** (`.gitattributes`), no longer git-ignored.
  HF upgrades LFS to Xet storage server-side.
- **`*.setup.json` is pruned, never cached.** Lake writes one per module (~1.8 MB with
  `import Mathlib.Tactic`) = 174 GB of the 187 GB build dir. `Module.checkArtifactsExist`
  checks `.olean`/`.ilean`/`.c` but *not* `setup.json`, so deleting them is safe.
  `.c` files (2.5 GB) **must** be kept or Lake rebuilds the module.
- **`defaultFacets = ["leanArts"]` is a dead end** — it is already the Lake default, and `.c`
  output is produced unconditionally as part of every module's artifacts.
- **Templates are soft-contract**: the runner requires only a template name + a selection
  (`--all`/`--bucket`/`--seq`); unknown `--flags` are forwarded verbatim to the template as
  private params; `--force` lets templates overwrite existing files (first application needs
  it because `oeis-gen` sorry skeletons already exist).
- **Generic math lives in `OEISLib`, generated files only pass parameters**: per-sequence
  `Defs.lean`/`Equiv_<hash>.lean` contain just the step list + calls into
  `OEISLib.Walk3.count` / `.aux` / `.countDp` and `countDp_eq_count`.
- **Walk3 is parameterized by `List Pnt`, not `Finset Pnt`** — `Finset.toList`/`Multiset.toList`
  are noncomputable and poison every definition downstream. Duplicate list entries
  double-count, exactly like duplicate summands do in the Wolfram program.
- **Wolfram recognition marks only the matched prefix.** The recognizer anchors at the start
  of the joined `%t` text and stops after the template's final `}]`; anything after (extra
  `a[n_] := ...` recurrences in A151162/A151254) stays unrecognized on purpose.
- **Step-set double-entry check**: steps parsed from the title and steps derived from the
  recursion offsets (negated) must agree, else the sequence fails loudly instead of being
  marked.
- **Runner verifies before writing**: a script-side DP transcription of the Wolfram code is
  evaluated for n = 0..min(TableRange, terms-1, cap=12) and compared with `sequence.data`;
  any mismatch aborts without writing files or marking the DB.
- **DB rows for Wolfram snippets use `source_tag='T'`**, hash = `formulaHash` of the matched
  `%t` substring (so `Equiv_<hash>.lean` ↔ formula row ↔ DB stay tied together);
  `sequence.formalized_formula_hashes` gets the hash merged in.
- **STATUS_VERIFIED vs PROVED for T-rows**: `formula_eq` is machine-proved, but the link to
  OEIS data is only checked computationally (`Data.lean` still `sorry`), so templates record
  `STATUS_VERIFIED`; upgrade later once `data_eq` lands.
- **Name templates use positional slot placeholders** (`{pK}` integer constant, `{AK}`
  sequence reference; number words normalized to digits). Grouping compares skeletons only —
  a value-equality-aware variant (self-composition vs cross-composition) was tried and
  rejected: it fragments big families without producing better ≥25 groups.

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
- `List.sum` takes **no function argument** (it is plain monoid sum); `s.sum f` exists only
  for `Finset`. Write `(l.map f).sum` or roll a `sumWith f l := (l.map f).sum`.
- `Finset.toList` / `Multiset.toList` are **noncomputable** — parameterize generic defs by
  `List` if you need runtime evaluation.
- `Array.get?` does not exist as a dot-name; use `a[i]?`. `String.toArray` likewise; use
  `s.toList.toArray`.
- `s!"..."` must be followed *directly* by the string literal — `s!(...)` fails to parse.
  Line continuations `\` inside interpolated strings are fine.
- `where` is a reserved word — not usable as a `let` name or column-ish identifier.
- Match patterns are lowercase `some`/`none` (`Some` is not a Lean 4 constructor).
- `rw` cannot rewrite under binders; for goals like `∑ x ∈ s, ...` with the target inside
  `fun x => ...`, use pointwise `simp only [h]` lemmas or `sumWith_congr`-style helpers.
- `Finset.sum_ite_eq` matches `if a = x` (a fixed), `Finset.sum_ite_eq'` matches
  `if x = a` — pick by orientation.
- `if_pos`/`if_neg` are deprecated in favor of `ite_eq_left`/`ite_eq_right` (warnings only).
- Kernel `decide` on small finset/list membership goals (as emitted into generated
  `Equiv_<hash>.lean`) is fast; deciding whole evaluated data lists hits maxRecDepth.

## Open items / next steps

1. **More templates** (see `Metadata/templates.txt` mining): N² end-on-vertical-axis (129),
   N² start-at-origin (77), N² start&end-at-origin (38), outlier A274969 — same runner, new
   `Scripts/Templates/<Name>.lean` + registry entry each. Corpus-wide candidate list with
   frequencies: `Scripts/templates.txt` (704 name templates ≥25 members; top: Galebach
   coordination 6070, Coxeter words 2302, sqrt-CF family ~2900 across 3 rows, primes ≡ a mod
   b 979, decimal expansions of fractions 960).
2. **Fill `Data.lean` for walkN3 sequences**: `data_eq` still `sorry`; once proved (interval
   cases over the DP), upgrade T-row statuses to reflect it.
3. **OEIS adapter:** map `Axxxxxx → [main def, .fn, .fz]` via
   `Alt.constApp` + `Registry.overlay`, feed `%F` lines + `sequence.data` through
   `Formula.findAll`, store formalized formulas back into the DB.
4. **Validate the prune+cache round trip on the `cache_test` branch.**
5. Multi-line `%F` blocks (`... (Start)` / `... (End)`) are currently split into one row per
   line. Group them before treating each line as a standalone formula.
6. Parser stage 2: Prop targets, recurrences/self-reference, limits, derivatives, filtered
   sums (`k | n`), Wolfram/LaTeX frontends onto the same AST.
7. `tabl`/`tabf` sequences currently get the flattened one-argument API only; the real
   two-argument version is deferred.
8. Build cost: `import Mathlib.Tactic` in every generated file makes a full 396k-sequence build
   impractical. Revisit if the A000 bucket build turns out too slow.
9. Consider exporting the DB to Parquet/JSONL — HF's dataset viewer cannot read SQLite.
10. The extra Wolfram recurrences in A151162/A151254 (appended `a[n_]` formulas) remain
    unformalized — candidates for the generic parser / future templates.
11. Parser gaps surfaced by the parse report: lone-constant formulas (`a(n) = 0`) fall below
    `minNodes` and are never segmented; lines containing several formulas can validate on a
    partial sub-formula (A000008's `h(n) = round((n+4)^2/20)` passed 8-term data check).

## Progress log

- **2026-08-27** — Extended `Scripts/OeisParseReport.lean` from `LIMIT 10` to `LIMIT 100` and regenerated the parse sweep (per user request ≥1000 formulas). `findFirst? (.arr .nat .int)` + `native_decide` over ≤8 terms, timed per line. Result on 1153 lines: 22 ok (1.9%) / 1131 fail (98.1%), ~548 s total. Added grouped report `/tmp/opencode/formula_parse_report_1000_groups.md` (16 heuristic syntax buckets: cross-ref `Axxxxxx` 27.9% (316), self-recurrence 16.1% (182), G.f. 11.1% (125), sum/product binders 9.5% (108), table/markers 7.7% (87), etc.; see file for per-group examples, avg/max times). No parser code changed — only the generator's `LIMIT` and output paths.

- **2026-08-26** — Added `Scripts/OeisParseReport.lean` (standalone, run via `lake env lean`,
  not in any lakefile glob; nothing else changed). For each of the first 10 sequences
  (A000001–A000010) it feeds every raw `%F` line unchanged to
  `Formula.findFirst? line (.arr .nat .int)` (builtin registry, no A-number overlay), times
  each line with `IO.monoMsNow`, validates candidates against the first ≤8 Int-fitting data
  terms (offset-shifted) and writes `/tmp/opencode/formula_parse_report.{md,csv}`.
  Result: 204 lines / 3 ok (A000007 floor(1/(n+1)) + (1-(-1)^2^n)/2, A000008 partial
  round((n+4)^2/20)) / 201 fail, ~69 s total. Failure classes: prose/table/conditional-case
  lines, self-recurrences, A-number references without overlay, and lone constants
  (`a(n) = 0`) which fall below the parser's `minNodes` segmentation threshold by design.
  Recipes discovered: (a) running DB access inside a compile-time `run_cmd` requires
  preloading leansqlite's FFI symbols:
  `lake env lean --load-dynlib=.lake/packages/leansqlite/.lake/build/lib/libleansqlite.so \
   --load-dynlib=.lake/packages/leansqlite/.lake/build/lib/lean/leansqlite_SQLite_FFI.so <file>`;
  (b) kernel `decide` gets stuck reducing `Int.floor`/`Rat` chains — data validation must use
  `native_decide` (compiler IR evaluation); (c) dot-chain `jsonArr s.toList.filterMap f`
  mis-elaborates — parenthesize `(jsonArr s).toList.filterMap f`; (d) `Exception.toString`
  doesn't exist, use `e.toMessageData.toString`.

- **2026-08-26** — Verified `OEISLib/Walk3.lean` compiles (`lake build OEISLib.Walk3`,
  success; two known `if_pos`/`if_neg` deprecation warnings remain, see gotchas).

- **2026-08-26** — Mined **all `%N` title templates corpus-wide** and saved the miner as
  `Scripts/name_templates.py` (user-requested; earlier pass left no script). Method: extract
  every `%N` line (398,534), normalize titles — lowercase, spelled-out number words → digits
  (`twenty-one`→21, `once`→1), `Annnnnn` refs → `{AK}` slots, integer literals → `{pK}`
  positional slots — group identical skeletons, keep ≥25 members, sort by frequency into
  `Scripts/templates.txt` (markdown table, count + template + 5 spread example IDs per row).
  Result: 245,149 distinct skeletons; **704 templates ≥25 covering 66,238 sequences
  (16.6%)**. Top: Galebach coordination sequences (6070), Coxeter reduced words (2302),
  duplicate-of (1214), primes ≡ p1 mod p2 (979), sqrt-CF trio (~2900 combined), decimal
  expansion of fractions (960). Complements the regex-based `Metadata/templates.txt`
  (27 hand-curated matchers): this one is a raw frequency inventory. Spot-verified against
  grep: divisors-of-N =580, continued-fraction-sqrt =966, Gal.* =6070 — exact matches.
  Rejected variant: value-equality slots (distinguishing `A064413(A064413(n))` from cross
  refs) — fragments families, no better groups. Script is standalone python3, CLI:
  `--seq-dir/--names-file/--out/--min-count`; regenerating the file is deterministic.

- **2026-08-26** — Re-mined templates corpus-wide per user request (no analysis scripts;
  headers combined into one file `/tmp/opencode/tpl/all_headers.txt`, sorted by
  A-number-stripped title, paged through chunk by chunk; families verified with `grep -c`).
  `Metadata/templates.txt` rewritten as **pure CSV `regex,frequency`**, 27 templates ≥25,
  sorted desc. Top: Coordination sequence Gal.* (6070), Hardin "Number of ... arrays"
  sub-templates (king 1390, diag-sum-diff 384, avoiding-3x3 287, symmetric-connected
  123-282, perimeter-pattern 218, neighbor-count 359+229, row sums 114), step-set walks
  (3254/129/77/38), 1/k-the-number-of (594), Sum_{k=0..floor} binomial (425/591),
  Decimal expansion of log_b(x) (482), n^k mod m (188), k-th cyclotomic polynomial (126),
  Smallest-k-digit-of-b^k (74), Central terms of triangle (53), k-almost primes (44),
  edge covers (37). Gotchas: GNU grep `\d`/`\s` fail inside ERE groups (use `[0-9]`,
  `[[:space:]]`); `a(X)|(Y)b` alternation splits the whole pattern — wrap alternatives.

- **2026-08-26** — Built the generic **template runner** and applied the first template
  end-to-end. New: `OEISLib` lean_lib with `OEISLib/Walk3.lean` (high-level `count` =
  endpoints-list of octant walks; low-level `aux`/`countDp` = faithful transcription of the
  Bostan–Kauers Wolfram `aux`/`Table[Sum]`; `countDp_eq_count` fully proved under
  steps ⊆ `unitCube`, no sorry, standard axioms only); `Scripts/OeisTemplate.lean` exe +
  `Scripts/OeisTemplate/Registry.lean` (Context/Template/markFormalized) +
  `Scripts/Templates/{Registry,WalkN3}.lean`. walkN3 run on **all 3254 N^3-octant-walk
  sequences in 12.6s: ok=3254 failed=0**; every sequence's DP verified against OEIS data
  before writing; A151162/A151254's appended `a[n_]` recurrences correctly left
  unformalized. DB: 3254 formula rows source_tag='T' STATUS_VERIFIED with
  verification_values, sequence.formalized_formula_hashes filled. Spot-built 12 generated
  modules incl. both outliers — all compile, `formula_eq` axiom-clean. Runner semantics:
  name+selection mandatory, unknown flags forwarded to template (`--table-max=`,
  `--check-cap=`), `--force` to override the oeis-gen sorry skeletons, `--dry-run`,
  `--limit`. Debugging recipe that found the two recognizer bugs (literal-space matching,
  missing `]; Table[` bracket): sed-strip `private` into a scratch copy + stage-by-stage
  Option-chain trace, then converted `recognize` to `Except String` so failures self-report.
- **2026-08-26** — Mined step-set walk template families (`%N` lines containing `steps taken
  from {`) into `Metadata/templates.txt`. Two independent extraction passes (grep pass +
  Python glob pass), both found exactly 3499 titles. Canonicalization merges `(0,0)`/`(0, 0)`
  spacing, optional commas before "and consisting", trailing periods, and the steps-count
  arithmetic (`n`, `2n`, `2 n`, `2*n`, `4 n` → `<K>*n`). Result: **4 templates with ≥25
  members cover 3498 of 3499**: N^3-octant walks (3254), N^2 end-on-vertical-axis (129),
  N^2 start-at-origin (77), N^2 start&end-at-origin (38); plus outlier A274969 (1). Every
  regex in the file is machine-verified to match exactly its member set. All scratch scripts
  live in /tmp/opencode/tpl/; only `Metadata/templates.txt` was created in the repo.

- **2026-08-26** — Reported raw-%F→AST→Lean mapping by re-running the parser standalone on
  the Tests.lean inputs (`lake env lean /tmp/opencode/Dump*.lean`). Confirmed: attribution
  stripping, paren auto-close, unicode normalization, canonical +/- reordering, braced vs
  paren sum styles unify, A-numbers resolve via Registry overlay to
  `∑ k ∈ Finset.range (n+1), Seq k`, PNat/subtype binders become `.val` projections,
  self-reference yields no term.
- **2026-08-26** — FormulaParser test suite fully green (`lake build FormulaParser.Tests` →
  "Build completed successfully"; segmentation/arithmetic/binders/api1/api2 all pass).
  Last bug was `let cfg2 : Config` — ambiguous between `Meta.Config` and `Formula.Config`
  after `open Lean Meta` — which error-recovered the whole `testsApi2` def into `sorry`, and
  the interpreter then refused to evaluate the runner ("depends on 'sorry' axiom"). Diagnosis
  recipe that worked: standalone scan command iterating `env.constants` for `value?.hasSorry`.
  Removed scratch `FormulaParser/Dbg.lean`. Parser stage 1 complete.
- **2026-08-26** — Implemented the stage-1 formula parser (OEIS.md §PARSER): new isolated
  lean_lib `FormulaParser/` (imports Lean core only; elaboration layer needs Mathlib in the
  caller's env). Modules: Basic (Ty lattice/coercions/Config), Ast (IR + signed-sum
  canonicalization), Lex (unicode-normalizing tokenizer; `_Name_` attributions become
  boundaries), Grammar (piece split, paren auto-close recovery, parse-everywhere + weighted-DP
  selection, Pratt parser incl. sum/product/integral binder forms), Registry (typed
  alternatives: multi-interpretation arithmetic incl. zpow, sqrt/log/floor/binomial/...;
  `Alt.constApp` for OEIS A-number wiring), Search (type-directed capped candidate generation,
  lossy floor/round finalizations only at result position), Elab (src→Syntax→elabTerm with
  mvar/sorry guards), Parser (`findAll`/`findFirst?`/`parseAll`/`parseAst`). Tests:
  `FormulaParser/Tests.lean`, ~36 tests in four groups run as separate scoped-heartbeat
  commands; data validation via kernel `decide`. Toolchain gotchas discovered: multiline
  record literals don't parse inside `partial def` bodies or `where` blocks; `mergeSort` needs
  `≤` comparators for stable ties; `run_cmd` takes only a doSeq; postfix `!` notation
  unavailable → use `Nat.factorial`; `whnfR` does not unfold regular defs (use kernel `decide`
  for data checks); ascriptions do coerce on the numeric tower; `Nat.log` is curried
  (`Nat.log base val`).
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
- **2026-08-20** — Planned the Hugging Face migration. Measured: `.lake/build` 189 GB (98k of
  792k modules), of which `ir/` is 178 GB; oleans 9.6 GB; `LOEIS/` 4.6 GB / 792,809 files;
  Mathlib is *not* in `.lake/build` (it lives in `.lake/packages/mathlib/.lake/build`, 6.5 GB).
  Confirmed oeisdata upstream is `github.com/oeis/oeisdata` (`seq/` 398,471 entries,
  `files/` 275,775). Un-ignored `oeisdata` and `Metadata/*.db`, added `.gitattributes` LFS rule,
  rewrote README setup section (clone → elan → sparse oeisdata → LFS database).
- **2026-08-20** — Read Lake's `Build/Module.lean`: `.c` is emitted unconditionally and is part
  of `checkArtifactsExist`, but `*.setup.json` is not — and it is 174 GB of the 187 GB build
  dir. Added `oeis-cache` (`prune`/`stat`/`put`/`get`), reverted oeisdata to a manual sparse
  clone, documented disk-usage strategy and cache download in README.
- **2026-08-20** — Added Hugging Face dataset card to README.md: YAML metadata block with
  `dataset_info`, feature descriptions (name, title, offset, data, formulas, keywords), split
  info (396,006 sequences), download/dataset size, license (CC0-1.0), tags, task IDs. Resolves
  HF warning "empty or missing yaml metadata in repo card".
- **2026-08-20** — Fixed README.md YAML validation errors: changed `language` from invalid
  "lean4" to valid "code" (special value for code/programming datasets), changed `license`
  from cc-by-sa-4.0 to cc0-1.0 (proper for OEIS), removed invalid `task_ids`
  "sequence-annotation", added complete `dataset_info` with feature descriptions.
- **2026-08-20** — Simplified README.md dataset card by removing empty `dataset_info` section.
  Kept minimal YAML: language, license, pretty_name, size_categories, source_datasets, tags.
- **2026-08-20** — Updated license in README.md YAML metadata to cc-by-sa-4.0 per user
  specification: Creative Commons Attribution Share-Alike 4.0.
- **2026-08-26** — Built **Coxeter template** end-to-end. New: `OEISLib/Coxeter.lean` (generic rational G.f. via `numCoeffs`/`denCoeffs`, power-series division `coxSeqAux`/`coxSeq`, `coeffsUpTo`/`coeffsUpTo_getElem`) and `Scripts/Templates/Coxeter.lean` (title `(g,r)` parser, `%F` joined-G.f. + `%t`/`%o` recognizers for `G.f.` rational/factored, recurrence, `coxG`, `CoefficientList[Series]`, PARI `Vec`, Magma `PowerSeriesRing`). Full run `--all --force`: **2302 ok, 0 failed** (2290 with ≥1 Equiv covering `gf-rational`/`gf-factored`/`recurrence`/`wolfram-series`/`wolfram-coxG`/`pari-vec`/`magma-series`, 12 `g=3` atypical G.f. with only `Defs.lean`). DB: `formula` rows `STATUS_VERIFIED` (`F` 2528, `O` 730, `T` 5541 total), `sequence.formalized_formula_hashes` filled. Spot-built `A162740`/`A166679`/`A168930`/`A170270`/`A169452` — all compile, `formula_eq` via `coeffsUpTo_getElem` bridge.
- **2026-08-26** — Created `TEMPLATES.md` per user request: documents only user-stated template requirements (high-level `Defs.lean`, similar `%F`/`%t`/`%o` → simple parser → computable `Equiv`, skip one-offs for generic parser, share general code in `OEISLib`, mark every formula/program in existing `oeis.db` tables). Uses `walkN3`/`coxeter` as examples, no new requirements added.
- **2026-08-26** — Renamed `coxeter` Equiv file's alternative definition from `programList`/`programList_eq`/`recurrence_holds`/`gfNum`/`gfDen` (custom names) to standard `formula`/`formula_eq` (with `formula_rfl`). Requirement from user: Equiv files must expose `formula` and `formula_eq` as other templates do. Updated `Scripts/Templates/Coxeter.lean:324` and `TEMPLATES.md:22` accordingly; regenerated all 2302 Equivs with `lake exe oeis-template coxeter --all --force` and verified `A162740`/`A166679`/`A168930` compile and `formula` is present in `oeis.db`.
- **2026-08-26** — Updated `TEMPLATES.md:4` per user clarification: even if a formula/program does not appear in *all* members but appears in **at least 20–30** and is very similar/generalizable, it is still worth parsing — the template just checks per sequence which ones contain it. One-offs (few sequences) remain for the generic parser.

## RULE 0 reminder

Repeating [RULE 0](#rule-0--keep-this-file-up-to-date-mandatory) as promised:

> **After every user prompt you act on, update this file** — append to the progress log, refresh
> the current state / schema / commands sections, and re-prioritize the open items. Do this
> before you end your turn, every time, without being asked.
