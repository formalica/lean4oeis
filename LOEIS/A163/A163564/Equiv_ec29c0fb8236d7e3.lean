import LOEIS.A163.A163564.Defs

/-!
# A163564 — program transcriptions (`Equiv_ec29c0fb8236d7e3`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(435*t^5 - 29*t^4 - 29*t^3 - 29*t^2 - 29*t + 1). a(n) = 29*a(n-1)+29*a(n-2)+29*a(n-3)+29*a(n-4)-435*a(n-5). - _Wesley Ivan Hurt_, May 11 2021` (gf-rational)
* `%F a(n) = 29*a(n-1)+29*a(n-2)+29*a(n-3)+29*a(n-4)-435*a(n-5). - _Wesley Ivan Hurt_, May 11 2021` (recurrence)
* `%T With[{num=Total[2t^Range[4]]+t^5+1, den=Total[-29 t^Range[4]]+435t^5+1}, CoefficientList[Series[num/den,{t,0,20}],t]] (* _Harvey P. Dale_, Sep 16 2011 *)` (wolfram-series)
* `%T CoefficientList[Series[(1+x)*(1-x^5)/(1-30*x+464*x^5-435*x^6), {x,0,20}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^5)/(1-30*x+464*x^5-435*x^6)) \\ _G. C. Greubel_, Jul 28 2017` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^5)/(1-30*x+464*x^5-435*x^6) )); // _G. C. Greubel_, May 18 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163564

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163564 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A163564 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163564
