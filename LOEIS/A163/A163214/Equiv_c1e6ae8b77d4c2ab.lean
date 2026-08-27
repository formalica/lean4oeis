import LOEIS.A163.A163214.Defs

/-!
# A163214 — program transcriptions (`Equiv_c1e6ae8b77d4c2ab`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(435*t^4 - 29*t^3 - 29*t^2 - 29*t + 1). a(n) = 29*(a(n-1) + a(n-2) + a(n-3) - 15*a(n-4)). - _G. C. Greubel_, Apr 28 2019` (gf-rational)
* `%F a(n) = 29*(a(n-1) + a(n-2) + a(n-3) - 15*a(n-4)). - _G. C. Greubel_, Apr 28 2019` (recurrence)
* `%T coxG[{4,435,-29}]` (wolfram-coxG)
* `%T CoefficientList[Series[(t^4+2*t^3+2*t^2+2*t+1)/(435*t^4-29*t^3-29*t^2 - 29*t+1), {t,0,20}], t] (* or *) LinearRecurrence[{29,29,29,-435}, {1,31, 930,27900,836535}, 20] (* _G. C. Greubel_, Dec 10 2016 *)` (wolfram-series)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^4)/(1-30*x+464*x^4-435*x^5)) \\ _G. C. Greubel_, Dec 10 2016, modified Apr 28 2019` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^4)/(1-30*x+464*x^4-435*x^5) )); // _G. C. Greubel_, Apr 28 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163214

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163214 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A163214 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163214
