import LOEIS.A163.A163503.Defs

/-!
# A163503 — program transcriptions (`Equiv_3f1b6ba230f18d07`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(190*t^5 - 19*t^4 - 19*t^3 - 19*t^2 - 19*t + 1). a(n) = 19*a(n-1)+19*a(n-2)+19*a(n-3)+19*a(n-4)-190*a(n-5). - _Wesley Ivan Hurt_, May 10 2021` (gf-rational)
* `%F a(n) = 19*a(n-1)+19*a(n-2)+19*a(n-3)+19*a(n-4)-190*a(n-5). - _Wesley Ivan Hurt_, May 10 2021` (recurrence)
* `%T coxG[{5,190,-19}]` (wolfram-coxG)
* `%T CoefficientList[Series[(1+x)*(1-x^5)/(1-20*x+209*x^5-190*x^6), {x,0,20}], x] (* _G. C. Greubel_, Jul 26 2017 *)` (wolfram-series)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^5)/(1-20*x+209*x^5-190*x^6)) \\ _G. C. Greubel_, Jul 26 2017` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^5)/(1-20*x+209*x^5-190*x^6) )); // _G. C. Greubel_, May 16 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163503

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163503 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A163503 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163503
