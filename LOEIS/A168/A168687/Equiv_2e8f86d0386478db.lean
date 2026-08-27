import LOEIS.A168.A168687.Defs

/-!
# A168687 — program transcriptions (`Equiv_2e8f86d0386478db`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/ (36*t^17 - 8*t^16 - 8*t^15 - 8*t^14 - 8*t^13 - 8*t^12 - 8*t^11 - 8*t^10 - 8*t^9 - 8*t^8 - 8*t^7 - 8*t^6 - 8*t^5 - 8*t^4 - 8*t^3 - 8*t^2 - 8*t + 1). G.f.: (1+t)*(1-t^17)/(1 -9 *t + 44*t^17 - 36*t^18). - _G. C. Greubel_, Mar 24 2021` (gf-rational)
* `%F G.f.: (t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/ (36*t^17 - 8*t^16 - 8*t^15 - 8*t^14 - 8*t^13 - 8*t^12 - 8*t^11 - 8*t^10 - 8*t^9 - 8*t^8 - 8*t^7 - 8*t^6 - 8*t^5 - 8*t^4 - 8*t^3 - 8*t^2 - 8*t + 1). G.f.: (1+t)*(1-t^17)/(1 -9 *t + 44*t^17 - 36*t^18). - _G. C. Greubel_, Mar 24 2021` (gf-factored)
* `%T coxG[{17,36,-8}]` (wolfram-coxG)
* `%T CoefficientList[Series[(1+t)*(1-t^17)/(1 -9*t +44*t^17 -36*t^18), {t, 0, 50}], t] (* _G. C. Greubel_, Aug 03 2016; Mar 24 2021 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168687

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168687 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A168687 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168687
