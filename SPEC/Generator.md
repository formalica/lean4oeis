# Generator — `lake exe oeis-gen`

Reads `Metadata/oeis.db` and writes the per-sequence skeleton files. Every
emitted declaration is a `sorry` placeholder; templates and the formula
parser later fill in real definitions.

Code: `Scripts/OeisGen.lean` (CLI, DB query, file writing, aggregators),
`Scripts/OeisGen/Render.lean` (pure string templates: `ArgKind`, `Names`,
`renderDefs`, `renderData`).

CLI:

```
lake exe oeis-gen --all
lake exe oeis-gen --bucket A000
lake exe oeis-gen --seq A000001 [--seq ...] [--force]
```

Selection: `--all`, one or more `--bucket`, or one or more `--seq`;
`--force` overwrites existing files (otherwise existing files are kept).

Output paths: `LOEIS/<name>.take 4 / <name>/Defs.lean` and `Data.lean`.

Skeleton content is exactly the file shape specified in
[OEISLib.md](OEISLib.md):

- index type from the offset (`0 → Nat`, `1 → PNat`, `k ≥ 2 → Nat` subtype,
  `k < 0 → Int` subtype);
- `RetType` = `Int` if any listed term starts with `-`, else `Nat`;
- `tabl` sequences get the flat API (`flat`, `flatFn`, `flatFz`, …);
  `tabf` sequences are skipped;
- decimal sequences (`cons` keyword) get the constant + flat-digit skeleton;
- `Data.lean` lists all terms and emits the data-equivalence theorems with
  bound hypotheses for the data range.

After writing per-sequence files the run rebuilds the aggregators from the
filesystem: `LOEIS/<bucket>/Defs.lean` and `LOEIS/<bucket>/Data.lean` import
every sequence in the bucket, and `LOEIS/Defs.lean`, `LOEIS/Data.lean`
import every bucket.
