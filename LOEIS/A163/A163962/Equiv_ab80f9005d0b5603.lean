import LOEIS.A163.A163962.Defs

/-!
# A163962 — program transcriptions (`Equiv_ab80f9005d0b5603`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(91*t^6 - 13*t^5 - 13*t^4 - 13*t^3 - 13*t^2 - 13*t + 1). G.f.: (1+x)*(1-x^6)/(1 -14*x +104*x^6 -91*x^7). - _G. C. Greubel_, Apr 25 2019` (gf-rational)
* `%F G.f.: (t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(91*t^6 - 13*t^5 - 13*t^4 - 13*t^3 - 13*t^2 - 13*t + 1). G.f.: (1+x)*(1-x^6)/(1 -14*x +104*x^6 -91*x^7). - _G. C. Greubel_, Apr 25 2019` (gf-factored)
* `%T CoefficientList[Series[(1+x)*(1-x^6)/(1-14*x+104*x^6-91*x^7), {x, 0, 20}], x] (* _G. C. Greubel_, Aug 13 2017, modified Apr 25 2019 *)` (wolfram-series)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^6)/(1-14*x+104*x^6-91*x^7)) \\ _G. C. Greubel_, Aug 13 2017, modified Apr 25 2019` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^6)/(1-14*x+104*x^6-91*x^7) )); // _G. C. Greubel_, Apr 25 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163962

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163962 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A163962 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163962
