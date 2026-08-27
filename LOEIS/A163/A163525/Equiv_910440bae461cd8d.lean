import LOEIS.A163.A163525.Defs

/-!
# A163525 — program transcriptions (`Equiv_910440bae461cd8d`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(276*t^5 - 23*t^4 - 23*t^3 - 23*t^2 - 23*t + 1). a(n) = 23*a(n-1)+23*a(n-2)+23*a(n-3)+23*a(n-4)-276*a(n-5). - _Wesley Ivan Hurt_, May 10 2021` (gf-rational)
* `%F a(n) = 23*a(n-1)+23*a(n-2)+23*a(n-3)+23*a(n-4)-276*a(n-5). - _Wesley Ivan Hurt_, May 10 2021` (recurrence)
* `%T CoefficientList[Series[(1+x)*(1-x^5)/(1-24*x+299*x^5-276*x^6), {x, 0, 20}], x] (* _G. C. Greubel_, Jul 27 2017 *)` (wolfram-series)
* `%T coxG[{5, 276, -23}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^5)/(1-24*x+299*x^5-276*x^6)) \\ _G. C. Greubel_, Jul 27 2017` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^5)/(1-24*x+299*x^5-276*x^6) )); // _G. C. Greubel_, May 16 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163525

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163525 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A163525 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163525
