import LOEIS.A163.A163217.Defs

/-!
# A163217 — program transcriptions (`Equiv_caa74ae69d5b0a47`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(528*t^4 - 32*t^3 - 32*t^2 - 32*t + 1). From _G. C. Greubel_, Apr 28 2019: (Start) a(n) = 32*(a(n-1) + a(n-2) + a(n-3)) - 528*a(n-4). G.f.: (1+x)*(1-x^4)/(1 - 33*x + 560*x^4 - 528*x^5). (End)` (gf-rational)
* `%F G.f.: (t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(528*t^4 - 32*t^3 - 32*t^2 - 32*t + 1). From _G. C. Greubel_, Apr 28 2019: (Start) a(n) = 32*(a(n-1) + a(n-2) + a(n-3)) - 528*a(n-4). G.f.: (1+x)*(1-x^4)/(1 - 33*x + 560*x^4 - 528*x^5). (End)` (gf-factored)
* `%F a(n) = 32*(a(n-1) + a(n-2) + a(n-3)) - 528*a(n-4).` (recurrence)
* `%T CoefficientList[Series[(t^4+2*t^3+2*t^2+2*t+1)/(528*t^4-32*t^3-32*t^2 - 32*t+1), {t,0,20}], t] (* or *)` (wolfram-series)
* `%T coxG[{4,528,-32}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^4)/(1-33*x+560*x^4-528*x^5)) \\ _G. C. Greubel_, Dec 11 2016, modified Apr 28 2019` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^4)/(1-33*x+560*x^4-528*x^5) )); // _G. C. Greubel_, Apr 28 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163217

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163217 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A163217 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163217
