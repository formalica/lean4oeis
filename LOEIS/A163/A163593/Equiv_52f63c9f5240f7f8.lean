import LOEIS.A163.A163593.Defs

/-!
# A163593 — program transcriptions (`Equiv_52f63c9f5240f7f8`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(528*t^5 - 32*t^4 - 32*t^3 - 32*t^2 - 32*t + 1). a(n) = 32*a(n-1)+32*a(n-2)+32*a(n-3)+32*a(n-4)-528*a(n-5). - _Wesley Ivan Hurt_, May 11 2021` (gf-rational)
* `%F a(n) = 32*a(n-1)+32*a(n-2)+32*a(n-3)+32*a(n-4)-528*a(n-5). - _Wesley Ivan Hurt_, May 11 2021` (recurrence)
* `%T coxG[{5,528,-32}]` (wolfram-coxG)
* `%T CoefficientList[Series[(1+x)*(1-x^5)/(1-33*x+560*x^5-528*x^6), {x, 0, 20}], x] (* _G. C. Greubel_, Jul 29 2017 *)` (wolfram-series)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^5)/(1-33*x+560*x^5-528*x^6)) \\ _G. C. Greubel_, Jul 29 2017` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^5)/(1-33*x+560*x^5-528*x^6) )); // _G. C. Greubel_, Apr 28 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163593

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163593 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A163593 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163593
