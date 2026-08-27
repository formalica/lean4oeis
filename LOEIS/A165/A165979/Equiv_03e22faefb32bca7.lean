import LOEIS.A165.A165979.Defs

/-!
# A165979 — program transcriptions (`Equiv_03e22faefb32bca7`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(325*t^10 - 25*t^9 - 25*t^8 - 25*t^7 - 25*t^6 - 25*t^5 - 25*t^4 - 25*t^3 - 25*t^2 - 25*t + 1). G.f.: (1+x)*(1-x^10)/(1 -26*x +350*x^10 -325*x^11). - _G. C. Greubel_, Apr 26 2019` (gf-rational)
* `%F G.f.: (t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(325*t^10 - 25*t^9 - 25*t^8 - 25*t^7 - 25*t^6 - 25*t^5 - 25*t^4 - 25*t^3 - 25*t^2 - 25*t + 1). G.f.: (1+x)*(1-x^10)/(1 -26*x +350*x^10 -325*x^11). - _G. C. Greubel_, Apr 26 2019` (gf-factored)
* `%T CoefficientList[Series[(1+x)*(1-x^10)/(1 -26*x +350*x^10 -325*x^11), {x, 0, 20}], x] (* _G. C. Greubel_, Apr 20 2016, modified Apr 26 2019 *)` (wolfram-series)
* `%T coxG[{10, 325, -25}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^10)/(1 -26*x +350*x^10 -325*x^11)) \\ _G. C. Greubel_, Apr 26 2019` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^10)/(1 -26*x +350*x^10 -325*x^11) )); // _G. C. Greubel_, Apr 26 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A165979

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A165979 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A165979 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A165979
