import LOEIS.A163.A163175.Defs

/-!
# A163175 — program transcriptions (`Equiv_887ff51e854f4157`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(276*t^4 - 23*t^3 - 23*t^2 - 23*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^4 + 2 t^3 + 2 t^2 + 2 t + 1)/(276 t^4 - 23 t^3 - 23 t^2 - 23 t + 1), {t, 0, 20}], t] (* _Jinyuan Wang_, Mar 23 2020 *)` (wolfram-series)
* `%T coxG[{4,276,-23}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163175

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163175 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A163175 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163175
