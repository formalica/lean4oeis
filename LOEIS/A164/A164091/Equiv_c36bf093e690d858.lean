import LOEIS.A164.A164091.Defs

/-!
# A164091 — program transcriptions (`Equiv_c36bf093e690d858`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(780*t^6 - 39*t^5 - 39*t^4 - 39*t^3 - 39*t^2 - 39*t + 1). G.f.: (1+x)*(1-x^6)/(1 -40*x +819*x^6 -780*x^7). - _G. C. Greubel_, Apr 25 2019` (gf-rational)
* `%F G.f.: (t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(780*t^6 - 39*t^5 - 39*t^4 - 39*t^3 - 39*t^2 - 39*t + 1). G.f.: (1+x)*(1-x^6)/(1 -40*x +819*x^6 -780*x^7). - _G. C. Greubel_, Apr 25 2019` (gf-factored)
* `%T coxG[{6,780,-39}]` (wolfram-coxG)
* `%T CoefficientList[Series[(1+x)*(1-x^6)/(1-40*x+819*x^6-780*x^7), {x,0,20}], x] (* _G. C. Greubel_, Apr 25 2019 *)` (wolfram-series)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^6)/(1-40*x+819*x^6-780*x^7)) \\ _G. C. Greubel_, Apr 25 2019` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^6)/(1-40*x+819*x^6-780*x^7) )); // _G. C. Greubel_, Apr 25 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A164091

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A164091 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A164091 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A164091
