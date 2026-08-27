import LOEIS.A163.A163397.Defs

/-!
# A163397 — program transcriptions (`Equiv_646a3c489246a09b`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(36*t^5 - 8*t^4 - 8*t^3 - 8*t^2 - 8*t + 1). a(n) = 8*a(n-1)+8*a(n-2)+8*a(n-3)+8*a(n-4)-36*a(n-5). - _Wesley Ivan Hurt_, May 10 2021` (gf-rational)
* `%F a(n) = 8*a(n-1)+8*a(n-2)+8*a(n-3)+8*a(n-4)-36*a(n-5). - _Wesley Ivan Hurt_, May 10 2021` (recurrence)
* `%T CoefficientList[Series[(1+x)*(1-x^5)/(1-9*x+44*x^5-36*x^6), {x, 0, 30}], x] (* or *) LinearRecurrence[{8,8,8,8,-36}, {1,10,90,810,7290,65565}, 30] (* _G. C. Greubel_, Dec 21 2016 *)` (wolfram-series)
* `%T coxG[{5, 36, -8}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^30)); Vec((1+x)*(1-x^5)/(1-9*x+44*x^5-36*x^6)) \\ _G. C. Greubel_, Dec 21 2016` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 30); Coefficients(R!( (1+x)*(1-x^5)/(1-9*x+44*x^5-36*x^6) )); // _G. C. Greubel_, May 12 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163397

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 30

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 30 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163397 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 30).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 30 n h'
  have h2 : A163397 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163397
