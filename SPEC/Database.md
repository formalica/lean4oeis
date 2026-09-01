# Database

`Metadata/oeis.db` is a SQLite database (created by `oeis-ingest`,
git-ignored / LFS). Schema lives in `Scripts/OeisIngest/Db.lean`. Two tables.

## `sequence` — one row per OEIS sequence

| Column | Set by | Contents |
| --- | --- | --- |
| `name` | ingest | `Axxxxxx`, PRIMARY KEY |
| `title` | ingest | the `%N` line |
| `offset` | ingest | first number of the `%O` line (SQL keyword, quoted) |
| `offset_first_big` | ingest | second number of `%O` (index of first term with abs value > 1), may be NULL |
| `keywords` | ingest | JSON array of the `%K` keywords (`cons`, `tabl`, `tabf`, …) |
| `data` | ingest | JSON array of term strings, in OEIS listing order (bare integer numerals) |
| `data_count` | ingest | number of terms |
| `source_file` | ingest | path of the source `.seq` file |
| `updated_at` | ingest | timestamp of the last ingest refresh |
| `main_definition_hash` | formalization | hash of the formula chosen as the main definition (empty until set) |
| `formalized_formula_hashes` | formalization | JSON array of hashes of formulas already formalized |
| `unformalized_formula_hashes` | ingest, trimmed by formalization | JSON array of hashes of formulas not yet formalized |
| `all_unformalized_formulas_text` | ingest, trimmed by formalization | JSON array of the raw texts of the not-yet-formalized formulas; ingest stores all `%F` texts, formalization removes a text once its formula is handled |
| `status` | formalization | `STATUS_UNKNOWN` until a stage updates it |

## `formula` — one row per formula

Primary key `(oeis_name, hash)`; `hash = formulaHash(human_written_formula)`
(see [OEISLib.md](OEISLib.md#hashes-of-equiv--basic-files)).

| Column | Contents |
| --- | --- |
| `hash` | `formulaHash` of the original unformalized text |
| `oeis_name` | owning sequence |
| `human_written_formula` | the original text |
| `formalized_formula` | the generated Lean code (empty until formalized) |
| `type` | `computable_definition`, `prop_definition`, or `basic_theorem` |
| `status` | `STATUS_UNKNOWN`, `STATUS_VERIFIED` (checked on data values, proof still `sorry`), or `STATUS_PROVED` |
| `verification_values` | JSON array of values at which the formula was checked |
| `disproved_values` | JSON array of values contradicting the formula |
| `additional_conditions` | JSON array of extra domain conditions (e.g. validity only for `n ≥ 2`) |
| `source_tag` | `F` (`%F` formula), `T` (`%t` Wolfram), `O` (`%o` other program) |
| `line_index` | line/snippet position in the source record (may be NULL) |

Indexes: `formula(hash)`, `formula(status)`, `sequence(status)`.

## Refresh semantics

Re-running ingest upserts OEIS-derived columns only (`title`, `offset`,
`keywords`, `data`, …) and inserts new `formula` rows; columns written by
formalization stages (`formalized_formula`, `type`, `status`,
`verification_values`, `main_definition_hash`, `formalized_formula_hashes`,
…) are preserved on conflict.
