import LOEIS.A163.A163404.Defs

/-!
# A163404 — program transcriptions (`Equiv_5c868fe5fd56d3d5`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(45*t^5 - 9*t^4 - 9*t^3 - 9*t^2 - 9*t + 1). a(n) = 9*a(n-1)+9*a(n-2)+9*a(n-3)+9*a(n-4)-45*a(n-5). - _Wesley Ivan Hurt_, May 10 2021` (gf-rational)
* `%F a(n) = 9*a(n-1)+9*a(n-2)+9*a(n-3)+9*a(n-4)-45*a(n-5). - _Wesley Ivan Hurt_, May 10 2021` (recurrence)
* `%T CoefficientList[Series[(1 + x)*(1-x^5)/(1-10*x+54*x^5-45*x^6), {x, 0, 30}], x] (* or *) LinearRecurrence[{9, 9, 9, 9, -45}, {1, 11, 110, 1100, 11000, 109945}, 30] (* _G. C. Greubel_, Dec 21 2016 *)` (wolfram-series)
* `%T coxG[{5, 45, -9}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^30)); Vec((1+x)*(1-x^5)/(1-10*x+54*x^5-45*x^6)) \\ _G. C. Greubel_, Dec 21 2016` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 30); Coefficients(R!( (1+x)*(1-x^5)/(1-10*x+54*x^5-45*x^6) )); // _G. C. Greubel_, May 12 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163404

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 30

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 30 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163404 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 30).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 30 n h'
  have h2 : A163404 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163404
