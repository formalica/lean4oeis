import LOEIS.A162.A162983.Defs

/-!
# A162983 — program transcriptions (`Equiv_97997ac5fcd4e408`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(36*t^4 - 8*t^3 - 8*t^2 - 8*t + 1). From _G. C. Greubel_, Apr 28 2019: (Start) a(n) = 8*(a(n-1) + a(n-2) + a(n-3)) - 36*a(n-4). G.f.: (1+x)*(1-x^4)/(1 - 9*x + 44*x^4 - 36*x^5). (End)` (gf-rational)
* `%F G.f.: (t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(36*t^4 - 8*t^3 - 8*t^2 - 8*t + 1). From _G. C. Greubel_, Apr 28 2019: (Start) a(n) = 8*(a(n-1) + a(n-2) + a(n-3)) - 36*a(n-4). G.f.: (1+x)*(1-x^4)/(1 - 9*x + 44*x^4 - 36*x^5). (End)` (gf-factored)
* `%F a(n) = 8*(a(n-1) + a(n-2) + a(n-3)) - 36*a(n-4).` (recurrence)
* `%T CoefficientList[Series[(1+x)*(1-x^4)/(1-9*x+44*x^4-36*x^5), {x,0,20}], x]` (wolfram-series)
* `%T (* or *) coxG[{4, 36, -8}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^4)/(1-9*x+44*x^4-36*x^5)) \\ _G. C. Greubel_, Apr 28 2019` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^4)/(1-9*x+44*x^4-36*x^5) )); // _G. C. Greubel_, Apr 28 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A162983

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A162983 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A162983 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A162983
