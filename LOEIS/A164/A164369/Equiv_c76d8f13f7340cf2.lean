import LOEIS.A164.A164369.Defs

/-!
# A164369 — program transcriptions (`Equiv_c76d8f13f7340cf2`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(15*t^7 - 5*t^6 - 5*t^5 - 5*t^4 - 5*t^3 - 5*t^2 - 5*t + 1). G.f.: (1+x)*(1-x^7)/(1 -6*x +20*x^7 -15*x^8). - _G. C. Greubel_, Apr 25 2019` (gf-rational)
* `%F G.f.: (t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(15*t^7 - 5*t^6 - 5*t^5 - 5*t^4 - 5*t^3 - 5*t^2 - 5*t + 1). G.f.: (1+x)*(1-x^7)/(1 -6*x +20*x^7 -15*x^8). - _G. C. Greubel_, Apr 25 2019` (gf-factored)
* `%T CoefficientList[Series[(1+x)*(1-x^7)/(1-6*x+20*x^7-15*x^8), {x, 0, 30}], x] (* _G. C. Greubel_, Sep 17 2017, modified Apr 25 2019 *)` (wolfram-series)
* `%T coxG[{7, 15, -5, 30}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^30)); Vec((1+x)*(1-x^7)/(1-6*x+20*x^7-15*x^8)) \\ _G. C. Greubel_, Sep 17 2017, modified Apr 25 2019` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 30); Coefficients(R!( (1+x)*(1-x^7)/(1-6*x+20*x^7-15*x^8) )); // _G. C. Greubel_, Apr 25 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A164369

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 30

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 30 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A164369 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 30).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 30 n h'
  have h2 : A164369 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A164369
