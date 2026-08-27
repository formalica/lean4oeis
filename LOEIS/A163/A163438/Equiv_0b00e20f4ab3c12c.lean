import LOEIS.A163.A163438.Defs

/-!
# A163438 — program transcriptions (`Equiv_0b00e20f4ab3c12c`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(66*t^5 - 11*t^4 - 11*t^3 - 11*t^2 - 11*t + 1). a(n) = 11*a(n-1)+11*a(n-2)+11*a(n-3)+11*a(n-4)-66*a(n-5). - _Wesley Ivan Hurt_, May 10 2021` (gf-rational)
* `%F a(n) = 11*a(n-1)+11*a(n-2)+11*a(n-3)+11*a(n-4)-66*a(n-5). - _Wesley Ivan Hurt_, May 10 2021` (recurrence)
* `%T CoefficientList[Series[(1+x)*(1-x^5)/(1-12*x+77*x^5-66*x^6), {x, 0, 10}], x] (* or *) LinearRecurrence[{11, 11, 11, 11, -66}, {1, 13, 156, 1872, 22464, 269490}, 30] (* _G. C. Greubel_, Dec 23 2016 *)` (wolfram-series)
* `%T coxG[{5, 66, -11}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^30)); Vec((1+x)*(1-x^5)/(1-12*x+77*x^5-66*x^6)) \\ _G. C. Greubel_, Dec 23 2016` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 30); Coefficients(R!( (1+x)*(1-x^5)/(1-12*x+77*x^5-66*x^6) )); // _G. C. Greubel_, May 12 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163438

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 10

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 10 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163438 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 10).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 10 n h'
  have h2 : A163438 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163438
