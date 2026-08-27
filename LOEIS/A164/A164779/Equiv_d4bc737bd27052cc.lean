import LOEIS.A164.A164779.Defs

/-!
# A164779 — program transcriptions (`Equiv_d4bc737bd27052cc`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 36*t^8 - 8*t^7 - 8*t^6 - 8*t^5 - 8*t^4 - 8*t^3 - 8*t^2 - 8*t + 1). G.f.: (1+x)*(1-x^8)/(1 -9*x +44*x^8 -36*x^9). - _G. C. Greubel_, Apr 26 2019` (gf-rational)
* `%F G.f.: (t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 36*t^8 - 8*t^7 - 8*t^6 - 8*t^5 - 8*t^4 - 8*t^3 - 8*t^2 - 8*t + 1). G.f.: (1+x)*(1-x^8)/(1 -9*x +44*x^8 -36*x^9). - _G. C. Greubel_, Apr 26 2019` (gf-factored)
* `%T coxG[{8,36,-8}]` (wolfram-coxG)
* `%T CoefficientList[Series[(1+x)*(1-x^8)/(1-9*x+44*x^8-36*x^9), {x,0,20}], x] (* _G. C. Greubel_, Apr 26 2019 *)` (wolfram-series)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^8)/(1-9*x+44*x^8-36*x^9)) \\ _G. C. Greubel_, Apr 26 2019` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^8)/(1-9*x+44*x^8-36*x^9) )); // _G. C. Greubel_, Apr 26 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A164779

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A164779 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A164779 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A164779
