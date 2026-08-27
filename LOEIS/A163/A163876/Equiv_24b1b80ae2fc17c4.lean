import LOEIS.A163.A163876.Defs

/-!
# A163876 — program transcriptions (`Equiv_24b1b80ae2fc17c4`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (x^6 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 2*x + 1)/(x^6 - x^5 - x^4 - x^3 - x^2 - x + 1). G.f.: (1+x)*(1-x^6)/(1-2*x+2*x^6-x^7). - _G. C. Greubel_, Apr 25 2019 a(n) = -a(n-6) + Sum_{k=1..5} a(n-k). - _Wesley Ivan Hurt_, May 07 2021` (gf-rational)
* `%F G.f.: (x^6 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 2*x + 1)/(x^6 - x^5 - x^4 - x^3 - x^2 - x + 1). G.f.: (1+x)*(1-x^6)/(1-2*x+2*x^6-x^7). - _G. C. Greubel_, Apr 25 2019 a(n) = -a(n-6) + Sum_{k=1..5} a(n-k). - _Wesley Ivan Hurt_, May 07 2021` (gf-factored)
* `%F a(n) = -a(n-6) + Sum_{k=1..5} a(n-k). - _Wesley Ivan Hurt_, May 07 2021` (recurrence)
* `%T coxG[{6,1,-1,40}]` (wolfram-coxG)
* `%T CoefficientList[Series[(1+x)*(1-x^6)/(1-2*x+2*x^6-x^7), {x,0,40}], x] (* _G. C. Greubel_, Aug 06 2017, modified Apr 25 2019 *)` (wolfram-series)
* `%O (PARI) x='x+O('x^40); Vec((x^6+2*x^5+2*x^4+2*x^3+2*x^2+2*x+1)/(x^6-x^5- x^4-x^3-x^2-x+1)) \\ _G. C. Greubel_, Aug 06 2017` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^6)/(1-2*x+2*x^6-x^7) )); // _G. C. Greubel_, Apr 25 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163876

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163876 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A163876 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163876
