# LOEIS

Formalizing OEIS sequences in Lean 4 + Mathlib. See [SPEC.md](SPEC.md) and [OEIS.md](OEIS.md)
for the design, and [AGENTS.md](AGENTS.md) for current project status.

## Setup

Install [elan](https://github.com/leanprover/elan) (the Lean version manager) if you don't
have it, then let it pick up the toolchain pinned in [lean-toolchain](lean-toolchain)
(`leanprover/lean4:v4.34.0-rc1`):

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
cd oeis-formal
elan toolchain install $(cat lean-toolchain)
lake exe cache get   # download prebuilt Mathlib .olean files instead of building from source
```

## Get the OEIS data

Raw sequence data (`oeisdata/seq/A<bucket>/A<number>.seq`, ~396k files, git-ignored) must be
present under [oeisdata/](oeisdata) before running the ingest step — see
[oeisdata/README.md](oeisdata/README.md) for how to obtain it.

## 1. Build the metadata database

Parses every `.seq` file into `Metadata/oeis.db` (SQLite, git-ignored):

```bash
lake build oeis-ingest
lake exe oeis-ingest
```

Add `--limit N` while iterating to only ingest the first N files. See
[AGENTS.md](AGENTS.md#commands) for the full flag list and database schema.

## 2. Generate the Lean skeletons

Reads `Metadata/oeis.db` and writes `LOEIS/<bucket>/<name>/{Defs,Data}.lean` (every declaration
is `sorry` at this stage):

```bash
lake build oeis-gen
lake exe oeis-gen --all
```

Useful variants:

```bash
lake exe oeis-gen --bucket A000               # one bucket
lake exe oeis-gen --seq A000001 --seq A000045 # specific sequences
lake exe oeis-gen --all --force               # overwrite already-generated files
```

`oeis-gen` never overwrites an existing file unless `--force` is passed, so it's safe to rerun
after later stages have replaced `sorry`s with real proofs.

## 3. Build everything

```bash
lake build
```

This compiles every generated sequence file plus the `LOEIS`/bucket aggregators. Expect
`declaration uses 'sorry'` warnings — that's expected until the formula formalization step
(see [AGENTS.md](AGENTS.md#open-items--next-steps)) is implemented.
