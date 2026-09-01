# Templates — `lake exe oeis-template`

A template formalizes a *family* of sequences (same math shape, different
constants) in one module. The generic runner provides all common machinery;
the template provides only family logic. Authoring guide: `TEMPLATES.md`.

Code: `Scripts/OeisTemplate.lean` (runner CLI) and
`Scripts/OeisTemplate/Registry.lean` (`Context`, `SeqInput`, `Outcome`,
`Template`, `markFormalized`); registered templates in
`Scripts/Templates/Registry.lean`; shared math for families lives in
`OEISLib/` (e.g. `OEISLib.Walk3`, `OEISLib.Coxeter`, `OEISLib.Residue`).

CLI:

```
lake exe oeis-template <template> --all
lake exe oeis-template <template> --bucket A147
lake exe oeis-template <template> --seq A147999 [--seq ...] [--force] [--dry-run]
```

Unknown flags are passed through to the template as private parameters.

A `Template` provides:

- `name` / `descr`;
- `selectWhere` — an SQL predicate over the `sequence` table selecting the
  family's candidates;
- `run : Context → SeqInput → IO Outcome` — processes one sequence and
  returns `ok` / `skipped` / `failed`.

Per sequence a template:

1. parses the constants out of the title;
2. recognizes the family-common formula/program shapes in the raw `.seq`
   text (`%F`, `%t`, `%o`); shapes that appear in at least ~20–30 members
   are worth handling; one-off formulas are left to the generic parser;
3. verifies the transcribed function against the sequence data (failure →
   `failed`, nothing is written or marked);
4. writes `Defs.lean` (real definition delegating to `OEISLib`) and, per
   recognized formula group, `Equiv_<hash>.lean` containing `formula` /
   `formula_eq` as specified in [OEISLib.md](OEISLib.md);
5. marks every recognized formula in the database via `markFormalized`
   (`formula` rows + `sequence.formalized_formula_hashes`).

`--dry-run` does steps 1–3 and reports without writing. A `failed` outcome
never marks the sequence as formalized.
