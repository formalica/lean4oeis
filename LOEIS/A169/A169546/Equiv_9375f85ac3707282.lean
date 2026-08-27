import LOEIS.A169.A169546.Defs

/-!
# A169546 — program transcriptions (`Equiv_9375f85ac3707282`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(6*t^35 - 3*t^34 - 3*t^33 - 3*t^32 - 3*t^31 - 3*t^30 - 3*t^29 - 3*t^28 - 3*t^27 - 3*t^26 - 3*t^25 - 3*t^24 - 3*t^23 - 3*t^22 - 3*t^21 - 3*t^20 - 3*t^19 - 3*t^18 - 3*t^17 - 3*t^16 - 3*t^15 - 3*t^14 - 3*t^13 - 3*t^12 - 3*t^11 - 3*t^10 - 3*t^9 - 3*t^8 - 3*t^7 - 3*t^6 - 3*t^5 - 3*t^4 - 3*t^3 - 3*t^2 - 3*t + 1). G.f.: (1+x)*(1-x^35)/(1 - 4*x + 9*x^35 - 6*x^36). - _G. C. Greubel_, Apr 25 2019` (gf-rational)
* `%F G.f.: (t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(6*t^35 - 3*t^34 - 3*t^33 - 3*t^32 - 3*t^31 - 3*t^30 - 3*t^29 - 3*t^28 - 3*t^27 - 3*t^26 - 3*t^25 - 3*t^24 - 3*t^23 - 3*t^22 - 3*t^21 - 3*t^20 - 3*t^19 - 3*t^18 - 3*t^17 - 3*t^16 - 3*t^15 - 3*t^14 - 3*t^13 - 3*t^12 - 3*t^11 - 3*t^10 - 3*t^9 - 3*t^8 - 3*t^7 - 3*t^6 - 3*t^5 - 3*t^4 - 3*t^3 - 3*t^2 - 3*t + 1). G.f.: (1+x)*(1-x^35)/(1 - 4*x + 9*x^35 - 6*x^36). - _G. C. Greubel_, Apr 25 2019` (gf-factored)
* `%T coxG[{35,6,-3,30}]` (wolfram-coxG)
* `%T CoefficientList[Series[(1+x)*(1-x^35)/(1-4*x+9*x^35-6*x^36), {x, 0, 25}], x] (* _G. C. Greubel_, Apr 25 2019 *)` (wolfram-series)
* `%O (PARI) my(x='x+O('x^25)); Vec((1+x)*(1-x^35)/(1-4*x+9*x^35-6*x^36)) \\ _G. C. Greubel_, Apr 25 2019` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 25); Coefficients(R!( (1+x)*(1-x^35)/(1-4*x+9*x^35-6*x^36) )); // _G. C. Greubel_, Apr 25 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A169546

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 25

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 25 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A169546 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 25).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 25 n h'
  have h2 : A169546 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A169546
