import LOEIS.A163.A163669.Defs

/-!
# A163669 — program transcriptions (`Equiv_22b9a1b53e1b8268`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(741*t^5 - 38*t^4 - 38*t^3 - 38*t^2 - 38*t + 1). a(n) = 38*a(n-1)+38*a(n-2)+38*a(n-3)+38*a(n-4)-741*a(n-5). - _Wesley Ivan Hurt_, May 11 2021` (gf-rational)
* `%F a(n) = 38*a(n-1)+38*a(n-2)+38*a(n-3)+38*a(n-4)-741*a(n-5). - _Wesley Ivan Hurt_, May 11 2021` (recurrence)
* `%T CoefficientList[Series[(1+x)*(1-x^5)/(1-39*x+779*x^5-741*x^6), {x, 0, 20}], x] (* _G. C. Greubel_, Aug 01 2017 *)` (wolfram-series)
* `%T coxG[{5, 741, -38}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^5)/(1-39*x+779*x^5-741*x^6)) \\ _G. C. Greubel_, Aug 01 2017` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^5)/(1-39*x+779*x^5-741*x^6) )); // _G. C. Greubel_, May 23 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163669

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163669 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A163669 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163669
