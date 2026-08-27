import LOEIS.A166.A166308.Defs

/-!
# A166308 — program transcriptions (`Equiv_f884679d93d7369b`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(1035*t^10 - 45*t^9 - 45*t^8 - 45*t^7 - 45*t^6 - 45*t^5 - 45*t^4 - 45*t^3 - 45*t^2 - 45*t + 1). G.f.: (1+x)*(1-x^10)/(1 -46*x +1080*x^10 -1035*x^11). - _G. C. Greubel_, Apr 25 2019` (gf-rational)
* `%F G.f.: (t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(1035*t^10 - 45*t^9 - 45*t^8 - 45*t^7 - 45*t^6 - 45*t^5 - 45*t^4 - 45*t^3 - 45*t^2 - 45*t + 1). G.f.: (1+x)*(1-x^10)/(1 -46*x +1080*x^10 -1035*x^11). - _G. C. Greubel_, Apr 25 2019` (gf-factored)
* `%T CoefficientList[Series[(1+x)*(1-x^10)/(1-46*x+1080*x^10-1035*x^11), {x, 0, 20}], x] (* _G. C. Greubel_, May 09 2016, modified Apr 25 2019 *)` (wolfram-series)
* `%T coxG[{10,1035,-45}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^10)/(1-46*x+1080*x^10 -1035*x^11)) \\ _G. C. Greubel_, Apr 25 2019` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^10)/(1-46*x+1080*x^10-1035*x^11) )); // _G. C. Greubel_, Apr 25 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166308

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166308 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A166308 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166308
