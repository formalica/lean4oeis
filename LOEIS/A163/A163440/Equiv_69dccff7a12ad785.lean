import LOEIS.A163.A163440.Defs

/-!
# A163440 — program transcriptions (`Equiv_69dccff7a12ad785`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(91*t^5 - 13*t^4 - 13*t^3 - 13*t^2 - 13*t + 1). a(n) = 13*a(n-1)+13*a(n-2)+13*a(n-3)+13*a(n-4)-91*a(n-5). - _Wesley Ivan Hurt_, May 10 2021` (gf-rational)
* `%F a(n) = 13*a(n-1)+13*a(n-2)+13*a(n-3)+13*a(n-4)-91*a(n-5). - _Wesley Ivan Hurt_, May 10 2021` (recurrence)
* `%T CoefficientList[Series[(1+x)*(1-x^5)/(1-14*x+104*x^5-91*x^6), {x, 0, 30}], x] (* or *) LinearRecurrence[{13, 13, 13, 13, -91}, {15, 210, 2940, 41160, 576135}, 30] (* _G. C. Greubel_, Dec 23 2016 *)` (wolfram-series)
* `%T coxG[{5, 91, -13}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^30)); Vec((1+x)*(1-x^5)/(1-14*x+104*x^5-91*x^6)) \\ _G. C. Greubel_, Dec 23 2016` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 30); Coefficients(R!( (1+x)*(1-x^5)/(1-14*x+104*x^5-91*x^6) )); // _G. C. Greubel_, May 12 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163440

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 30

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 30 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163440 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 30).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 30 n h'
  have h2 : A163440 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163440
