import LOEIS.A166.A166468.Defs

/-!
# A166468 — program transcriptions (`Equiv_bfc864f13cf75f56`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(3*t^12 - 2*t^11 - 2*t^10 - 2*t^9 - 2*t^8 - 2*t^7 - 2*t^6 - 2*t^5 - 2*t^4 - 2*t^3 - 2*t^2 - 2*t + 1). G.f.: (1+x)*(1-x^12)/(1 -3*x +5*x^12 -3*x^13). - _G. C. Greubel_, Apr 26 2019 a(n) = -3*a(n-12) + 2*Sum_{k=1..11} a(n-k). - _Wesley Ivan Hurt_, May 06 2021` (gf-rational)
* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(3*t^12 - 2*t^11 - 2*t^10 - 2*t^9 - 2*t^8 - 2*t^7 - 2*t^6 - 2*t^5 - 2*t^4 - 2*t^3 - 2*t^2 - 2*t + 1). G.f.: (1+x)*(1-x^12)/(1 -3*x +5*x^12 -3*x^13). - _G. C. Greubel_, Apr 26 2019 a(n) = -3*a(n-12) + 2*Sum_{k=1..11} a(n-k). - _Wesley Ivan Hurt_, May 06 2021` (gf-factored)
* `%F a(n) = -3*a(n-12) + 2*Sum_{k=1..11} a(n-k). - _Wesley Ivan Hurt_, May 06 2021` (recurrence)
* `%T CoefficientList[Series[(1+x)*(1-x^12)/(1 -3*x +5*x^12 -3*x^13), {x, 0, 30}], x ] (* _Vincenzo Librandi_, Apr 29 2014 *)(* modified by _G. C. Greubel_, Apr 26 2019 *)` (wolfram-series)
* `%T coxG[{12,3,-2,30}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^30)); Vec((1+x)*(1-x^12)/(1-3*x+5*x^12-3*x^13)) \\ _G. C. Greubel_, Apr 26 2019` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 30); Coefficients(R!( (1+x)*(1-x^12)/(1-3*x+5*x^12-3*x^13) )); // _G. C. Greubel_, Apr 26 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166468

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 30

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 30 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166468 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 30).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 30 n h'
  have h2 : A166468 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166468
