import LOEIS.A163.A163969.Defs

/-!
# A163969 — program transcriptions (`Equiv_eb641944ab2430f1`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(171*t^6 - 18*t^5 - 18*t^4 - 18*t^3 - 18*t^2 - 18*t + 1).` (gf-rational)
* `%T coxG[{6,171,-18}]` (wolfram-coxG)
* `%T CoefficientList[Series[(t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(171*t^6 - 18*t^5 - 18*t^4 - 18*t^3 - 18*t^2 - 18*t + 1), {t,0,50}], t] (* _G. C. Greubel_, Aug 23 2017 *)` (wolfram-series)
* `%O (PARI) t='t+O('t^50); Vec((t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(171*t^6 - 18*t^5 - 18*t^4 - 18*t^3 - 18*t^2 - 18*t + 1)) \\ _G. C. Greubel_, Aug 23 2017` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163969

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163969 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A163969 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163969
