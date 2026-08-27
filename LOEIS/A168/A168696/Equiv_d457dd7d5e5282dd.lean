import LOEIS.A168.A168696.Defs

/-!
# A168696 — program transcriptions (`Equiv_d457dd7d5e5282dd`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/ (153*t^17 - 17*t^16 - 17*t^15 - 17*t^14 - 17*t^13 - 17*t^12 - 17*t^11 - 17*t^10 - 17*t^9 - 17*t^8 - 17*t^7 - 17*t^6 - 17*t^5 - 17*t^4 - 17*t^3 - 17*t^2 - 17*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(153*t^17 - 17*t^16 - 17*t^15 - 17*t^14 - 17*t^13 - 17*t^12 - 17*t^11 - 17*t^10 - 17*t^9 - 17*t^8 - 17*t^7 - 17*t^6 - 17*t^5 - 17*t^4 - 17*t^3 - 17*t^2 - 17*t + 1), {t,0,50}], t] (* _G. C. Greubel_, Aug 03 2016 *)` (wolfram-series)
* `%T coxG[{17,153,-17}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168696

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168696 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A168696 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168696
