# Build and cache

## Lake targets (`lakefile.toml`)

- Library `LOEIS` — generated per-sequence files (`LOEIS.+`).
- Library `OEISLib` — shared math used by generated files.
- Library `FormulaParser` — the standalone formula parser (Lean/core only).
- Library `Scripts` — the executables' support code.
- Executables: `oeis-ingest`, `oeis-gen`, `oeis-template`, `oeis-cache`.

Generated files carry no per-file linter options; `unusedVariables` and
`style.longLine` are disabled repo-wide in `lakefile.toml` because skeletons
have unused binders and long term lists by construction.

## Build cache — `lake exe oeis-cache`

A full `.lake/build` is far too large to rebuild per checkout, so compiled
artifacts are archived:

```
lake exe oeis-cache prune   # delete regenerable *.setup.json (the bulk of build/)
lake exe oeis-cache stat    # artifact counts and sizes by extension
lake exe oeis-cache put     # write cache/loeis-build.tar.zst + cache/manifest.json
lake exe oeis-cache get     # restore .lake/build from the archive
```

Only `lib/` and the `.c` files under `ir/` are archived. Lake's
`Module.checkArtifactsExist` requires `.olean`, `.ilean` and `.c`, but never
`setup.json`; the `setup.json` files (~94% of the directory) are pruned and
rewritten on demand. The manifest records toolchain, lake-manifest and
lakefile hashes so a stale archive is detected on `get`.

## CI (`.github/workflows/`)

- `lean_action_ci.yml` — build on push/PR via `leanprover-community/lean-action`,
  plus Mathlib docgen for GitHub Pages.
- `create-release.yml` — Lean release tagging when `lean-toolchain` changes.
- `update.yml` — manual/optional dependency update check.

Raw OEIS data (`oeisdata/`) and `Metadata/oeis.db` are not built; they are
acquired separately and stored via Git LFS (see `README.md`).
