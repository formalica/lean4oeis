import LOEIS.A163.A163645.Defs

/-!
# A163645 — program transcriptions (`Equiv_c6b7087e2a23582a`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(630*t^5 - 35*t^4 - 35*t^3 - 35*t^2 - 35*t + 1). a(n) = -630*a(n-5) + 35*Sum_{k=1..4} a(n-k). - _Wesley Ivan Hurt_, May 05 2021` (gf-rational)
* `%F a(n) = -630*a(n-5) + 35*Sum_{k=1..4} a(n-k). - _Wesley Ivan Hurt_, May 05 2021` (recurrence)
* `%T CoefficientList[Series[(1+x)*(1-x^5)/(1-36*x+665*x^5-630*x^6), {x,0,20}], x] (* _G. C. Greubel_, Aug 01 2017 *)` (wolfram-series)
* `%T coxG[{5,630,-35}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^5)/(1-36*x+665*x^5-630*x^6)) \\ _G. C. Greubel_, Aug 01 2017` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^5)/(1-36*x+665*x^5-630*x^6) )); // _G. C. Greubel_, May 22 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163645

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163645 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A163645 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163645
