import LOEIS.A168.A168683.Defs

/-!
# A168683 — program transcriptions (`Equiv_0d465ec53369be47`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1) / (10*t^17 - 4*t^16 - 4*t^15 - 4*t^14 - 4*t^13 - 4*t^12 - 4*t^11 - 4*t^10 - 4*t^9 - 4*t^8 - 4*t^7 - 4*t^6 - 4*t^5 - 4*t^4 - 4*t^3 - 4*t^2 - 4*t + 1). G.f.: (1+t)*(1-t^17)/(1 -5*t +14*t^17 -10*t^18). - _G. C. Greubel_, Feb 22 2021` (gf-rational)
* `%F G.f.: (t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1) / (10*t^17 - 4*t^16 - 4*t^15 - 4*t^14 - 4*t^13 - 4*t^12 - 4*t^11 - 4*t^10 - 4*t^9 - 4*t^8 - 4*t^7 - 4*t^6 - 4*t^5 - 4*t^4 - 4*t^3 - 4*t^2 - 4*t + 1). G.f.: (1+t)*(1-t^17)/(1 -5*t +14*t^17 -10*t^18). - _G. C. Greubel_, Feb 22 2021` (gf-factored)
* `%T CoefficientList[Series[(1+t)*(1-t^17)/(1 -5*t +14*t^17 -10*t^18), {t, 0, 40}], t] (* _G. C. Greubel_, Aug 03 2016, Feb 22 2021 *)` (wolfram-series)
* `%T coxG[{17,10,-4,30}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168683

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 40

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 40 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168683 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 40).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 40 n h'
  have h2 : A168683 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168683
