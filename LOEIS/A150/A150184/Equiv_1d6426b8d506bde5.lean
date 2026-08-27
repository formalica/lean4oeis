import LOEIS.A150.A150184.Defs

/-!
# A150184 — low-level definition (`Equiv_1d6426b8d506bde5`)

Alternative definition transcribed from the `%t` Wolfram program (formalized in `oeis.db` under formula hash `1d6426b8d506bde5`):

```wolfram
aux[i_Integer, j_Integer, k_Integer, n_Integer] := Which[Min[i, j, k, n] < 0 || Max[i, j, k] > n, 0, n == 0, KroneckerDelta[i, j, k, n], True, aux[i, j, k, n] = aux[-1 + i, j, -1 + k, -1 + n] + aux[i, -1 + j, -1 + k, -1 + n] + aux[i, j, 1 + k, -1 + n] + aux[1 + i, 1 + j, -1 + k, -1 + n] + aux[1 + i, 1 + j, 1 + k, -1 + n]]; Table[Sum[aux[i, j, k, n], {i, 0, n}, {j, 0, n}, {k, 0, n}], {n, 0, 10}]
```

`dpCount` is the dynamic-programming transcription; `formula_eq` shows it coincides with the high-level walk-count main definition in `Defs.lean`.
-/

namespace A150184

/-- Low-level DP recursion (`aux`) specialized to `A150184`. -/
def dpAux : OEISLib.Walk3.Pnt → Nat → Nat :=
  OEISLib.Walk3.aux steps

/-- Low-level DP count: `Table[Sum[aux[i,j,k,n], {i,0,n}, {j,0,n}, {k,0,n}], ...]`
specialized to `A150184`. -/
def dpCount : Nat → Nat :=
  OEISLib.Walk3.countDp steps

/-- Every step of `A150184` lies in `{-1,0,1}^3`, which makes the pruning of the DP value-preserving. -/
theorem steps_in_unitCube : ∀ s ∈ steps, s ∈ OEISLib.Walk3.unitCube := by decide

/-- **formula_eq**: the low-level count equals the main (high-level) definition. -/
theorem formula_eq (n : Nat) : dpCount n = A150184 n :=
  OEISLib.Walk3.countDp_eq_count steps steps_in_unitCube n

end A150184
