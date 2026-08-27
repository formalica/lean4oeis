import LOEIS.A163.A163660.Defs

/-!
# A163660 — program transcriptions (`Equiv_2786080e69f59159`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(666*t^5 - 36*t^4 - 36*t^3 - 36*t^2 - 36*t + 1). a(n) = 36*a(n-1)+36*a(n-2)+36*a(n-3)+36*a(n-4)-666*a(n-5). - _Wesley Ivan Hurt_, May 11 2021` (gf-rational)
* `%F a(n) = 36*a(n-1)+36*a(n-2)+36*a(n-3)+36*a(n-4)-666*a(n-5). - _Wesley Ivan Hurt_, May 11 2021` (recurrence)
* `%T CoefficientList[Series[(1+x)*(1-x^5)/(1-37*x+702*x^5-666*x^6), {x,0,20}], x] (* _G. C. Greubel_, Aug 01 2017 *)` (wolfram-series)
* `%T coxG[{5, 666, -36}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^5)/(1-37*x+702*x^5-666*x^6)) \\ _G. C. Greubel_, Aug 01 2017` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^5)/(1-37*x+702*x^5-666*x^6) )); // _G. C. Greubel_, Apr 28 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163660

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163660 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A163660 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163660
