import LOEIS.A162.A162760.Defs

/-!
# A162760 — program transcriptions (`Equiv_1ab28334ec10de66`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^3 + 2*t^2 + 2*t + 1)/(45*t^3 - 9*t^2 - 9*t + 1). G.f.: (1+x)*(1-x^3)/(1 - 10*x + 54*x^3 - 45*x^4). - _G. C. Greubel_, Apr 26 2019` (gf-rational)
* `%F G.f.: (t^3 + 2*t^2 + 2*t + 1)/(45*t^3 - 9*t^2 - 9*t + 1). G.f.: (1+x)*(1-x^3)/(1 - 10*x + 54*x^3 - 45*x^4). - _G. C. Greubel_, Apr 26 2019` (gf-factored)
* `%T CoefficientList[Series[(1+x)*(1-x^3)/(1-10*x+54*x^3-45*x^4), {x,0,20}]` (wolfram-coxG)
* `%T CoefficientList[Series[(1+x)*(1-x^3)/(1-10*x+54*x^3-45*x^4), {x,0,20}],x] (* or *) coxG[{3, 45, -9}] (* The coxG program is at A169452 *) (* _G. C. Greubel_, Apr 26 2019 *)` (wolfram-series)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^3)/(1-10*x+54*x^3-45*x^4) )); // _G. C. Greubel_, Apr 26 2019` (magma-series)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^3)/(1-10*x+54*x^3-45*x^4)) \\ _G. C. Greubel_, Apr 26 2019` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A162760

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A162760 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A162760 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A162760
