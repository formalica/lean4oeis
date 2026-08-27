# Templates

How to create a new OEIS template. This follows only the requirements stated by the user.

## Requirements

1. **Example to follow**: `Scripts/Templates/WalkN3.lean` is the reference. It generates `Defs.lean` for the `walkN3` family and also formalizes one formula from the `%t` (Wolfram) section.

2. **Investigate the family**: Find sequences whose `%N` titles are the same up to constant parameters. Example: `Number of reduced words of length n in Coxeter group on g generators S_i with relations (S_i)^2 = (S_i S_j)^r = I` — about 2302 sequences.

3. **Main definition in `Defs.lean`**: Write a high-level *propositional* definition for the sequence and provide the computable version that `Defs.lean` delegates to. Keep it as the primary definition of the family.

4. **Similar formulas only**: From `%F` (formula), `%t` (Wolfram), `%o` (other languages) and similar sections, formalize only formulas/programs that are **very similar across many members of the family** (same shape with different constants like `g,r`). Write a **simple parser** for those shapes and from each generate a **computable formula** to put into `Equiv_<hash>.lean`. If a formula/program appears not in all sequences but appears in **at least 20–30 of them** and is very similar and can be generalized, it is still worth parsing — the script just checks per sequence which ones contain it and which do not. Formulas that occur for only a few sequences (one-offs) are skipped — they will be handled later by the generic parser.

5. **Share generic code in `OEISLib`**: If a theorem or function is general for all members and can be defined once and reused, put it in `OEISLib/<Name>.lean` and call it from each sequence's `Defs.lean` / `Equiv_<hash>.lean` with the concrete parameters. Do not duplicate the same math per sequence.

6. **Mark as formalized in `oeis.db`**: Every formalized formula and program must be marked in the existing tables (no new tables). `formula` rows and `sequence.formalized_formula_hashes` already exist and already cover formulas and programs in various languages — just insert/update rows there.

## What a template produces per sequence

- `LOEIS/<bucket>/<name>/Defs.lean` — imports the shared `OEISLib` library, defines parameters (e.g. `gParam`, `rParam`), defines the sequence `def Axxxxxx : argType → retType := OEISLib.<Lib>.func params`, plus `prop`, `fn`/`fz` and `*_correct`/`*_eq` theorems.
- `LOEIS/<bucket>/<name>/Equiv_<hash>.lean` — imports `Defs.lean`, transcribes each recognized similar formula/program as `def formula` (not a custom name) delegating to `OEISLib`, and proves `theorem formula_eq` (same names as other templates) as the bridge to the main definition. One file bundles all similar flavors for the sequence; `hash = formulaHash(concat matched texts)` / or per-snippet hash. Do not use custom names like `programList`/`dpCount` for the alternative definition — use `formula`/`formula_eq`.
- No `Basic_<hash>.lean` is needed for templates (those are for generic parser).

## How to add a new template

1. Create `OEISLib/<Name>.lean` if shared math is needed. Keep definitions `computable`, parameterised by the title constants, and prove the bridge lemmas once.
2. Create `Scripts/Templates/<Name>.lean`:
   - `parseTitle : String → Option Params` — extract constants from `%N`.
   - Simple whitespace-tolerant recognizers for each similar `%F`/`%t`/`%o` shape; return flavor + matched text + `source_tag` (`F`/`T`/`O`) + line index.
   - `recognizeAll` — run recognizers over the raw `.seq` text (join `%F` lines with spaces for split G.f.s if needed), dedup by flavor.
   - `verifyValues` — evaluate the shared `OEISLib` function for `n = 0 .. min(data.size-1, cap)` and compare to `sequence.data`; fail without writing or marking on mismatch.
   - `renderDefs` / `renderEquiv` — pure `String` builders. `renderEquiv` must define `def formula` and `theorem formula_eq` (not custom names like `programList` or `dpCount`).
   - `run : Context → SeqInput → IO Outcome` — parse title → find snippets → verify → write files (respect `ctx.force` / `ctx.dryRun`) → call `markFormalized` for each matched snippet.
   - `def template : Template` with `name`, `descr`, `selectWhere` (SQL predicate on `sequence.title`).
3. Register in `Scripts/Templates/Registry.lean`: import the new module and add to `templates` array.
4. Build and test: `lake build oeis-template`, `lake exe oeis-template <name> --seq Axxxxxx --dry-run --force`, then `--all --dry-run --force`, then `--all --force` and spot-build a few `LOEIS/.../Defs` + `Equiv_*`.
5. The runner handles CLI selection (`--all`/`--bucket`/`--seq`), `--force`/`--dry-run`, and `--check-cap` forwarding; no new `oeis.db` schema is needed.

## Existing examples

- `walkN3` (~3254): `OEISLib.Walk3` + `%t` Wolfram DP.
- `coxeter` (~2302): `OEISLib.Coxeter.coxSeq` (rational G.f. division) + `%F` G.f./recurrence + `%t` `coxG`/`CoefficientList[Series]` + `%o` PARI `Vec` + Magma `PowerSeriesRing`.

Specific one-off formulas are intentionally left unrecognized.
