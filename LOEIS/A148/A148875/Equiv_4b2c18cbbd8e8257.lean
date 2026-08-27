import LOEIS.A148.A148875.Defs

/-!
# A148875 — low-level definition (`Equiv_4b2c18cbbd8e8257`)

Alternative definition transcribed from the `%t` Wolfram program (formalized in `oeis.db` under formula hash `4b2c18cbbd8e8257`):

```wolfram
aux[i_Integer, j_Integer, k_Integer, n_Integer] := Which[Min[i, j, k, n] < 0 || Max[i, j, k] > n, 0, n == 0, KroneckerDelta[i, j, k, n], True, aux[i, j, k, n] = aux[-1 + i, j, k, -1 + n] + aux[-1 + i, 1 + j, k, -1 + n] + aux[i, -1 + j, 1 + k, -1 + n] + aux[1 + i, -1 + j, -1 + k, -1 + n] + aux[1 + i, j, -1 + k, -1 + n]]; Table[Sum[aux[i, j, k, n], {i, 0, n}, {j, 0, n}, {k, 0, n}], {n, 0, 10}]
```

`dpCount` is the dynamic-programming transcription; `formula_eq` shows it coincides with the high-level walk-count main definition in `Defs.lean`.
-/

namespace A148875

/-- Low-level DP recursion (`aux`) specialized to `A148875`. -/
def dpAux : OEISLib.Walk3.Pnt → Nat → Nat :=
  OEISLib.Walk3.aux steps

/-- Low-level DP count: `Table[Sum[aux[i,j,k,n], {i,0,n}, {j,0,n}, {k,0,n}], ...]`
specialized to `A148875`. -/
def dpCount : Nat → Nat :=
  OEISLib.Walk3.countDp steps

/-- Every step of `A148875` lies in `{-1,0,1}^3`, which makes the pruning of the DP value-preserving. -/
theorem steps_in_unitCube : ∀ s ∈ steps, s ∈ OEISLib.Walk3.unitCube := by decide

/-- **formula_eq**: the low-level count equals the main (high-level) definition. -/
theorem formula_eq (n : Nat) : dpCount n = A148875 n :=
  OEISLib.Walk3.countDp_eq_count steps steps_in_unitCube n

end A148875
