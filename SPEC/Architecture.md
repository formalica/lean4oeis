# Architecture

The pipeline turns raw OEIS records into checked Lean formalizations in five
stages. Each stage reads the artifacts of the previous one and never mutates
earlier artifacts.

```
oeisdata/seq/**.seq            (OEIS internal format, git-ignored raw data)
        │  lake exe oeis-ingest        Ingest.md
        ▼
Metadata/oeis.db               SQLite: sequence + formula tables   Database.md
        │  lake exe oeis-gen           Generator.md
        ▼
LOEIS/<bucket>/<name>/         Defs.lean + Data.lean skeletons (sorry)
        │
        ├─ lake exe oeis-template <name>   Templates.md
        │      (family-wide recognizers → real Defs.lean + Equiv_<hash>.lean)
        └─ FormulaParser library          FormulaParser.md
               (generic %F/%t/%o parsing → Equiv_<hash>.lean / Basic_<hash>.lean)
        │
        ▼  every new formula is checked against the data before it is kept
Verification.md  →  formula.status in oeis.db  (STATUS_VERIFIED / proved)
        │
        ▼  lake build LOEIS
BuildAndCache.md  (CI + .lake/build cache)
```

Components:

- **`Scripts/OeisIngest/`** — parser of the `.seq` record format and SQLite
  upsert logic. CLI: `lake exe oeis-ingest`.
- **`Scripts/OeisGen/`** — pure string renderers for the skeleton files and
  the bucket/library aggregators. CLI: `lake exe oeis-gen`.
- **`Scripts/Templates/`** + **`Scripts/OeisTemplate/`** — per-family
  formalizers and their generic runner. CLI: `lake exe oeis-template`.
- **`FormulaParser/`** — frontend-independent formula parser (Lean/core
  only); the generic per-formula formalizer.
- **`OEISLib/`** — shared mathematics used by generated files; generated
  sequence files delegate here instead of duplicating code.
- **`LOEIS/`** — generated per-sequence files; layout and naming are
  specified in [OEISLib.md](OEISLib.md).

Invariants across stages:

- Re-running ingest refreshes only OEIS-derived columns; formalization
  results (formalized formulas, statuses, hashes) survive.
- A generator/template run never silently keeps an unchecked formula: the
  verification step must accept it against the data or the sequence is left
  unmarked (see [Verification.md](Verification.md)).
- All output paths are deterministic: `LOEIS/<A-num take 4>/<A-num>/…`.
