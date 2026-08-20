---
language:
- code
license: cc-by-sa-4.0
pretty_name: LOEIS - Lean OEIS Formalization
size_categories:
- 100K<n<1M
source_datasets:
- OEIS
tags:
- mathematics
- formal-verification
- lean
- oeis
- sequence-formalization
---

# LOEIS

Formalizing OEIS sequences in Lean 4 + Mathlib. See [SPEC.md](SPEC.md) and [OEIS.md](OEIS.md)
for the design, and [AGENTS.md](AGENTS.md) for current project status.

## Setup

### 1. Clone this repository

```bash
git clone https://huggingface.co/datasets/formalica/lean4oeis
cd lean4oeis
```

This gives you the Lean sources and scripts only. The OEIS raw data and the metadata database
are fetched separately (next two steps) so that a plain clone stays small.

### 2. Install Lean

Install [elan](https://github.com/leanprover/elan) (the Lean version manager) if you don't
have it, then let it pick up the toolchain pinned in [lean-toolchain](lean-toolchain)
(`leanprover/lean4:v4.34.0-rc1`):

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
elan toolchain install $(cat lean-toolchain)
lake exe cache get   # download prebuilt Mathlib .olean files instead of building from source
```

### 3. Fetch the OEIS raw data (only if you want to rebuild the database)

[`oeisdata`](https://github.com/oeis/oeisdata) is registered as a submodule, but you only ever
need its `seq/` tree. Its `files/` tree holds 275,775 supporting-file entries that are useless
here, so fetch sparsely:

```bash
git clone --depth 1 --filter=blob:none --sparse \
  https://github.com/oeis/oeisdata.git oeisdata
git -C oeisdata sparse-checkout set seq
```

That downloads ~1.6 GB (398,471 `.seq` files under `oeisdata/seq/A<bucket>/A<number>.seq`)
instead of the full repository. To grab everything instead, use
`git submodule update --init --depth 1 oeisdata`.

### 4. Get the metadata database

`Metadata/oeis.db` (~360 MB) is stored with Git LFS. Either pull it from your clone:

```bash
git lfs install
git lfs pull --include="Metadata/oeis.db"
```

or download it directly without cloning:

```bash
mkdir -p Metadata
curl -L -o Metadata/oeis.db \
  https://huggingface.co/datasets/formalica/lean4oeis/resolve/main/Metadata/oeis.db
```

With the database in place you can skip straight to step 2 below — the raw OEIS data from
step 3 is only needed if you want to regenerate the database yourself.

## 1. Build the metadata database

Parses every `.seq` file into `Metadata/oeis.db` (SQLite, tracked with Git LFS):

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
