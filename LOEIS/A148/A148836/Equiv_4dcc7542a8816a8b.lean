import LOEIS.A148.A148836.Defs

/-!
# A148836 — low-level definition (`Equiv_4dcc7542a8816a8b`)

Alternative definition transcribed from the `%t` Wolfram program (formalized in `oeis.db` under formula hash `4dcc7542a8816a8b`):

```wolfram
aux[i_Integer, j_Integer, k_Integer, n_Integer] := Which[Min[i, j, k, n] < 0 || Max[i, j, k] > n, 0, n == 0, KroneckerDelta[i, j, k, n], True, aux[i, j, k, n] = aux[-1 + i, 1 + j, -1 + k, -1 + n] + aux[i, -1 + j, -1 + k, -1 + n] + aux[i, j, 1 + k, -1 + n] + aux[1 + i, j, k, -1 + n] + aux[1 + i, 1 + j, -1 + k, -1 + n]]; Table[Sum[aux[i, j, k, n], {i, 0, n}, {j, 0, n}, {k, 0, n}], {n, 0, 10}]
```

`dpCount` is the dynamic-programming transcription; `formula_eq` shows it coincides with the high-level walk-count main definition in `Defs.lean`.
-/

namespace A148836

/-- Low-level DP recursion (`aux`) specialized to `A148836`. -/
def dpAux : OEISLib.Walk3.Pnt → Nat → Nat :=
  OEISLib.Walk3.aux steps

/-- Low-level DP count: `Table[Sum[aux[i,j,k,n], {i,0,n}, {j,0,n}, {k,0,n}], ...]`
specialized to `A148836`. -/
def dpCount : Nat → Nat :=
  OEISLib.Walk3.countDp steps

/-- Every step of `A148836` lies in `{-1,0,1}^3`, which makes the pruning of the DP value-preserving. -/
theorem steps_in_unitCube : ∀ s ∈ steps, s ∈ OEISLib.Walk3.unitCube := by decide

/-- **formula_eq**: the low-level count equals the main (high-level) definition. -/
theorem formula_eq (n : Nat) : dpCount n = A148836 n :=
  OEISLib.Walk3.countDp_eq_count steps steps_in_unitCube n

end A148836
