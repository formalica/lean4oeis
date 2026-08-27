import LOEIS.A163.A163345.Defs

/-!
# A163345 — program transcriptions (`Equiv_1df36beaa98a73ba`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(15*t^5 - 5*t^4 - 5*t^3 - 5*t^2 - 5*t + 1). a(n) = 5*a(n-1)+5*a(n-2)+5*a(n-3)+5*a(n-4)-15*a(n-5). - _Wesley Ivan Hurt_, May 10 2021` (gf-rational)
* `%F a(n) = 5*a(n-1)+5*a(n-2)+5*a(n-3)+5*a(n-4)-15*a(n-5). - _Wesley Ivan Hurt_, May 10 2021` (recurrence)
* `%T CoefficientList[Series[(1+x)*(1-x^5)/(1-6*x+20*x^5-15*x^6), {x, 0, 30}], x] (* or *) LinearRecurrence[{5,5,5,5,-15}, {1,7,42,252,1512,9051}, 30] (* _G. C. Greubel_, Dec 19 2016 *)` (wolfram-series)
* `%T coxG[{5,15,-5}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^30)); Vec((1+x)*(1-x^5)/(1-6*x+20*x^5-15*x^6)) \\ _G. C. Greubel_, Dec 19 2016` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 30); Coefficients(R!( (1+x)*(1-x^5)/(1-6*x+20*x^5-15*x^6) )); // _G. C. Greubel_, May 12 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163345

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 30

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 30 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163345 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 30).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 30 n h'
  have h2 : A163345 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163345
