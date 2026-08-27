import LOEIS.A163.A163600.Defs

/-!
# A163600 — program transcriptions (`Equiv_245f2cc41feb731b`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(561*t^5 - 33*t^4 - 33*t^3 - 33*t^2 - 33*t + 1). a(n) = 33*a(n-1)+33*a(n-2)+33*a(n-3)+33*a(n-4)-561*a(n-5). - _Wesley Ivan Hurt_, May 11 2021` (gf-rational)
* `%F a(n) = 33*a(n-1)+33*a(n-2)+33*a(n-3)+33*a(n-4)-561*a(n-5). - _Wesley Ivan Hurt_, May 11 2021` (recurrence)
* `%T CoefficientList[Series[(1+x)*(1-x^5)/(1-34*x+594*x^5-561*x^6), {x, 0, 20}], x] (* _G. C. Greubel_, Jul 29 2017 *)` (wolfram-series)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^5)/(1-34*x+594*x^5-561*x^6)) \\ _G. C. Greubel_, Jul 29 2017` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^5)/(1-34*x+594*x^5-561*x^6) )); // _G. C. Greubel_, Apr 28 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163600

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163600 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A163600 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163600
