import LOEIS.A166.A166691.Defs

/-!
# A166691 — program transcriptions (`Equiv_da314bbcf286f166`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(703*t^12 - 37*t^11 - 37*t^10 - 37*t^9 -37*t^8 -37*t^7 -37*t^6 - 37*t^5 - 37*t^4 - 37*t^3 - 37*t^2 - 37*t + 1). G.f.: (1+x)*(1-x^12)/(1 -38*x +740*x^12 -703*x^13). - _G. C. Greubel_, Apr 26 2019 a(n) = -703*a(n-12) + 37*Sum_{k=1..11} a(n-k). - _Wesley Ivan Hurt_, May 06 2021` (gf-rational)
* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(703*t^12 - 37*t^11 - 37*t^10 - 37*t^9 -37*t^8 -37*t^7 -37*t^6 - 37*t^5 - 37*t^4 - 37*t^3 - 37*t^2 - 37*t + 1). G.f.: (1+x)*(1-x^12)/(1 -38*x +740*x^12 -703*x^13). - _G. C. Greubel_, Apr 26 2019 a(n) = -703*a(n-12) + 37*Sum_{k=1..11} a(n-k). - _Wesley Ivan Hurt_, May 06 2021` (gf-factored)
* `%F a(n) = -703*a(n-12) + 37*Sum_{k=1..11} a(n-k). - _Wesley Ivan Hurt_, May 06 2021` (recurrence)
* `%T CoefficientList[Series[(1+x)*(1-x^12)/(1-38*x+740*x^12-703*x^13), {x, 0, 20}], x] (* _G. C. Greubel_, May 23 2016, modified Apr 26 2019 *)` (wolfram-series)
* `%T coxG[{12,703,-37}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^12)/(1-38*x+740*x^12-703*x^13)) \\ _G. C. Greubel_, Apr 26 2019` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^12)/(1-38*x+740*x^12-703*x^13) )); // _G. C. Greubel_, Apr 26 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166691

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166691 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A166691 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166691
