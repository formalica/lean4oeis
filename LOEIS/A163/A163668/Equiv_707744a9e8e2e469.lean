import LOEIS.A163.A163668.Defs

/-!
# A163668 — program transcriptions (`Equiv_707744a9e8e2e469`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(703*t^5 - 37*t^4 - 37*t^3 - 37*t^2 - 37*t + 1). a(n) = 37*a(n-1)+37*a(n-2)+37*a(n-3)+37*a(n-4)-703*a(n-5). - _Wesley Ivan Hurt_, May 11 2021` (gf-rational)
* `%F a(n) = 37*a(n-1)+37*a(n-2)+37*a(n-3)+37*a(n-4)-703*a(n-5). - _Wesley Ivan Hurt_, May 11 2021` (recurrence)
* `%T CoefficientList[Series[(1+x)*(1-x^5)/(1-38*x+740*x^5-703*x^6), {x, 0, 20}], x] (* _G. C. Greubel_, Aug 01 2017 *)` (wolfram-series)
* `%T coxG[{5, 703, -37}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^5)/(1-38*x+740*x^5-703*x^6)) \\ _G. C. Greubel_, Aug 01 2017` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^5)/(1-38*x+740*x^5-703*x^6) )); // _G. C. Greubel_, May 23 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163668

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163668 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A163668 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163668
