import LOEIS.A164.A164681.Defs

/-!
# A164681 — program transcriptions (`Equiv_d71e496b191821a1`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (x^7 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 2*x + 1)/(703*x^7 - 37*x^6 - 37*x^5 - 37*x^4 - 37*x^3 - 37*x^2 - 37*x + 1). G.f.: (1+x)*(1-x^7)/(1 -38*x +740*x^7 -703*x^8). - _G. C. Greubel_, Apr 26 2019` (gf-rational)
* `%F G.f.: (x^7 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 2*x + 1)/(703*x^7 - 37*x^6 - 37*x^5 - 37*x^4 - 37*x^3 - 37*x^2 - 37*x + 1). G.f.: (1+x)*(1-x^7)/(1 -38*x +740*x^7 -703*x^8). - _G. C. Greubel_, Apr 26 2019` (gf-factored)
* `%T CoefficientList[Series[(x^7 + 2 x^6 + 2 x^5 + 2 x^4 + 2 x^3 + 2 x^2 + 2 x + 1)/(703 x^7 - 37 x^6 - 37 x^5 - 37 x^4 - 37 x^3 - 37 x^2 - 37 x + 1), {x, 0, 20}], x ] (* _Vincenzo Librandi_, Apr 29 2014 *)` (wolfram-series)
* `%T coxG[{7, 703, -37}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^7)/(1-38*x+740*x^7-703*x^8)) \\ _G. C. Greubel_, Apr 26 2019` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^7)/(1 -38*x +740*x^7 -703*x^8) )); // _G. C. Greubel_, Apr 26 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A164681

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A164681 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A164681 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A164681
