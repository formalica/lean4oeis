import LOEIS.A166.A166690.Defs

/-!
# A166690 — program transcriptions (`Equiv_46211fb1b00af6f1`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(666*t^12 - 36*t^11 - 36*t^10 - 36*t^9 -36*t^8 -36*t^7 -36*t^6 - 36*t^5 - 36*t^4 - 36*t^3 - 36*t^2 - 36*t + 1). G.f.: (1+x)*(1-x^12)/(1 -37*x +702*x^6 -666*x^7). - _G. C. Greubel_, Apr 26 2019 a(n) = -666*a(n-12) + 36*Sum_{k=1..11} a(n-k). - _Wesley Ivan Hurt_, May 06 2021` (gf-rational)
* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(666*t^12 - 36*t^11 - 36*t^10 - 36*t^9 -36*t^8 -36*t^7 -36*t^6 - 36*t^5 - 36*t^4 - 36*t^3 - 36*t^2 - 36*t + 1). G.f.: (1+x)*(1-x^12)/(1 -37*x +702*x^6 -666*x^7). - _G. C. Greubel_, Apr 26 2019 a(n) = -666*a(n-12) + 36*Sum_{k=1..11} a(n-k). - _Wesley Ivan Hurt_, May 06 2021` (gf-factored)
* `%F a(n) = -666*a(n-12) + 36*Sum_{k=1..11} a(n-k). - _Wesley Ivan Hurt_, May 06 2021` (recurrence)
* `%T CoefficientList[Series[(1+x)*(1-x^12)/(1-37*x+702*x^6-666*x^7), {x, 0, 20}], x] (* _G. C. Greubel_, May 23 2016, modified Apr 26 2019 *)` (wolfram-series)
* `%T coxG[{12, 666, -36}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^12)/(1-37*x+702*x^6-666*x^7)) \\ _G. C. Greubel_, Apr 26 2019` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^12)/(1-37*x+702*x^6-666*x^7) )); // _G. C. Greubel_, Apr 26 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166690

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166690 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A166690 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166690
