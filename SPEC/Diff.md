# Diff — what `main` has that this branch does not

Comparison of:

- **main** — `origin/main` @ `3914e50108c` ("feat: route LFS to Hugging Face";
  a squashed single commit, no common merge-base with this branch),
- **this branch** — `arena/01a04646-lean4oeis` @ `2a84ad10b86` ("feat: add
  templates to parse related sequences") plus the new `SPEC/` directory.

Main takes a different formalization route: instead of the Lean template
runner + the `FormulaParser` library, it adds a **Python LLM-agent pipeline**
that translates OEIS *program blocks* (Maple first) into Lean, validates
whole batches with one `lake build`, and records everything in new database
tables. Full design doc on main: `FORMALIZE.md`.

## 1. LLM-agent formalization pipeline — `Scripts/formalize/` (new, Python)

Package `oeis-formalize` (`pyproject.toml`, entry point
`python -m formalize` / `oeis-formalize`; deps: `pydantic`,
`pydantic-ai-slim[openai,google]`):

| Module | Role |
| --- | --- |
| `__main__.py` | CLI: `run`, `retry`, `show` subcommands; `--batch-size`, `--retry N`, `--learn`, `--keep-check-files`, `--include-attempted`, … |
| `agent.py` | pydantic-ai agent wiring (OpenAI/Google); deliberately no tools — Lean is always compiled by the pipeline |
| `pipeline.py` | batch orchestration: select → prompt → structured output → span resolution → render files → one `lake build` per batch → classify → write DB; repair rounds inside one conversation |
| `db.py` | SQLite access (`select_programs`, `group_batches`, `verified_definitions` — up to 3 already-verified alternative defs per referenced sequence) |
| `spans.py` | turns the model's `start_marker` / `end_marker` anchors into `[start,end)` spans of the raw block (≥6-char markers, non-overlap, backtracking over ambiguous anchors); computes uncovered **gaps** |
| `render.py` | renders `Equiv_<hash>.lean` and `Check/B<batch>/<seq>_<hash>.lean`; shape checks: exactly one `formula`, no `import`/`namespace`/`section`/`#eval`/`#check`/`#print`, helpers `formula_`-prefixed, no calls to the sequence's own A-number |
| `lean.py` | runs `lake build`, attributes diagnostics to individual items (rebuilds target alone if Lake stopped early), parses `OEIS_CHECK_FAIL` / `OEIS_DEP_RANGE` |
| `models.py` | structured output contract: `FormalizedProgram` (`oeis_name`, `start_marker`, `end_marker`, `lean_code`, `arg_kind ∈ {Nat,PNat,NatSub,Int,IntSub}`, `computable`, `note`), `SkippedProgram`, `BatchResult`; status constants |
| `prompt.py` | loads `Skills/<lang>/SKILL.md`, filters its function table to identifiers present in the batch (`*` rows always kept), assembles per-sequence context (title, offset, signature, terms, referenced sequences) |
| `view.py` | terminal rendering for `show` |
| `config.py` | paths and tuning knobs |
| `selftest.py` | package self-test |

Pipeline mechanics worth noting (see `FORMALIZE.md` on main):

- One LLM call handles a whole batch; one batch never contains two blocks of
  the same sequence; failures are fed back as a repair message in the same
  conversation; batches resume later from a stored `chat_history`.
- The model returns markers, not source echoes; the complement of resolved
  spans is recorded as gaps — non-trivial gaps are defects that block
  `BATCH_OK` (`STATUS_UNFORMALIZED` vs `STATUS_GAP_TRIVIAL`).
- Outcomes: `STATUS_VERIFIED`, `STATUS_COMPILE_ERROR`, `STATUS_EVAL_MISMATCH`,
  `STATUS_DEP_RANGE`, `STATUS_NONCOMPUTABLE` (stored, never compiled),
  `STATUS_REJECTED`; only verified items keep their `Equiv` file.
- `--learn` asks a second call for reusable knowledge → `skill_suggestion`
  rows, merged into the skill file by hand.

## 2. Batch validation library — `Check/` (new, Lean)

- `Check/Basic.lean` — `Oeis.Check.report name offset expected actual`:
  `#eval`s the translated formula over the known terms and throws
  `OEIS_CHECK_FAIL <name>: n=…: expected …, got …` on the first mismatch, so
  a wrong translation is a build error.
- Check modules are generated per batch as `Check/B<batch>/<seq>_<hash>.lean`;
  cross-sequence calls go through **data-backed shims** (the real `Axxxxxx`
  defs are still `sorry`) — a shim panics with `OEIS_DEP_RANGE` when the
  dependency needs a term OEIS does not list. Check modules are deleted after
  the batch is recorded unless `--keep-check-files`.
- `lakefile.toml` on main adds `Check` as a scratch `lean_lib` (not in
  `defaultTargets`).

## 3. Ingest of program blocks (`%p` / `%t` / `%o`)

`Scripts/OeisIngest/{Parse,Db}.lean` on main additionally parse program tags
into a new `program` table:

- `%p` → `maple`, `%t` → `mathematica`, `%o` → language taken from the
  `(Language)` marker (`pari`, `python`, `haskell`, …);
- consecutive same-tag lines form one verbatim block; `%p`/`%t` are never
  split (splitting merged programs is the LLM step's job), `%o` is cut at
  every language marker;
- `program(hash)` = 16 hex chars of `String.hash` of the block text.

New database tables (created by the Lean ingest schema, see
[Database.md](Database.md) for this branch's tables): `program`,
`formalization_batch` (model, status `BATCH_PENDING/RUNNING/OK/PARTIAL/FAILED`,
`chat_history`, filtered `skill_text`, …), `formalization_item` (per extracted
program: `formula_hash`, `original_text`, `span_start/end`, `lean_code`,
`arg_kind`, `computable`, `depends_on`, `status`, `failure_kind`,
`failure_points`, `compiler_output`, `verified_upto`, …), `skill_suggestion`,
`program_gap`.

Note the hash divergence: pipeline `Equiv_<hash>` files on main use
**blake2b-64** of the resolved program text; this branch uses
`hex(String.hash)` (see [OEISLib.md](OEISLib.md#hashes-of-equiv--basic-files)).

## 4. Skills and documentation

- `Skills/maple/SKILL.md` (new) — the Maple → Lean 4 translation instructions
  with a `<!-- BEGIN FUNCTION TABLE -->` Maple/Lean mapping that is filtered
  per batch; structured for future `Skills/<language>/`.
- `FORMALIZE.md` (new) — the full design/implementation document for the
  pipeline above (overview, ingest, batch selection, prompt, output
  contract, generated Lean, validation/classification, retry/resume, skill
  self-improvement, the new tables, commands, limitations).
- `.lfsconfig` (new) — Git LFS routed to Hugging Face
  (`https://huggingface.co/datasets/formalica/lean4oeis.git/info/lfs`).
- Updated `README.md`, `AGENTS.md`, `.gitignore`; `lakefile.toml` changed
  (see below).

## 5. Content removed on main (present in this branch)

- The whole **`FormulaParser/`** library (`Ast`, `Lex`, `Grammar`,
  `Registry`, `Basic`, `Search`, `Elab`, `Parser`, `Tests`).
- The Lean **template system**: `Scripts/OeisTemplate.lean`,
  `Scripts/OeisTemplate/Registry.lean`, `Scripts/Templates/`
  (`Coxeter`, `PrimeCongruent`, `WalkN3`, `Registry`) and the `oeis-template`
  exe; ~5,546 template-generated `Equiv_<hash>.lean` files (main has only 4,
  produced by the new pipeline).
- `OEISLib/` (`Coxeter.lean`, `Residue.lean`, `Walk3.lean`).
- `Scripts/OeisParseReport.lean`, `Scripts/name_templates.py`,
  `Scripts/templates.txt`, `Metadata/templates.txt`, `TEMPLATES.md`,
  `tmp_sample.lean`.
- Correspondingly, main's `lakefile.toml` drops the `FormulaParser` and
  `OEISLib` libraries and the `oeis-template` executable, and adds `Check`.

This branch also contains `SPEC/` (this documentation set), which does not
exist on main.
