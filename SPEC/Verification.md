# Verification

Every formula is checked against the data before it counts as formalized.
There are two levels:

1. **Data verification** — evaluate the formalized candidate at every index
   covered by the known terms and compare with `sequence.data`
   (offset-shifted; flat view for tables and decimal digits). A single
   mismatch rejects the formula. Templates do this inside `run` before
   writing files; the formula parser does it through its validation
   functor (`findFirst?` / `findAll` accept only candidates that pass).
   Checked values are recorded in `formula.verification_values`; mismatches
   in `disproved_values`.
2. **Proof** — the theorem in an `Equiv` / `Basic` file is either proved or
   closed with `sorry`. A `sorry` is allowed only after a concrete check
   (`interval_cases`, or `decide` / `norm_num` where applicable) that the
   statement holds for every data-covered index; this check must fail if a
   data point contradicts it.

Formula status (`formula.status` in the database):

- `STATUS_UNKNOWN` — not looked at.
- `STATUS_VERIFIED` — formalized and checked against the data; the proof is
  still `sorry` (guarded by the interval check).
- `STATUS_PROVED` — the Lean proof is complete (`formula_eq` for an
  alternative definition; the statement itself for a `Basic` theorem); the
  interval checks are removed once the real proof is in.

Main definition: if it is still `sorry`, the corresponding data-equivalence
theorem is `sorry` too; once the main definition is filled, its
`data_eq` family follows the same rules.

Non-general statements: a formula valid only on a subdomain (e.g. for
`n ≥ 2`) records that in `formula.additional_conditions`; the generated
theorem carries the condition as a hypothesis (or the definition handles
the excluded indices by explicit cases).
