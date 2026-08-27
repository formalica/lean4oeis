import LOEIS.A163.A163216.Defs

/-!
# A163216 — program transcriptions (`Equiv_a97fee435a82cdfd`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(496*t^4 - 31*t^3 - 31*t^2 - 31*t + 1). From _G. C. Greubel_, Apr 28 2019: (Start) a(n) = 31*(a(n-1) + a(n-2) + a(n-3) - 16*a(n-4)). G.f.: (1+x)*(1-x^4)/(1 - 32*x + 527*x^4 - 496*x^5). (End)` (gf-rational)
* `%F G.f.: (t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(496*t^4 - 31*t^3 - 31*t^2 - 31*t + 1). From _G. C. Greubel_, Apr 28 2019: (Start) a(n) = 31*(a(n-1) + a(n-2) + a(n-3) - 16*a(n-4)). G.f.: (1+x)*(1-x^4)/(1 - 32*x + 527*x^4 - 496*x^5). (End)` (gf-factored)
* `%F a(n) = 31*(a(n-1) + a(n-2) + a(n-3) - 16*a(n-4)).` (recurrence)
* `%T CoefficientList[Series[(t^4+2*t^3+2*t^2+2*t+1)/(496*t^4-31*t^3-31*t^2 - 31*t+1), {t,0,20}], t] (* or *) LinearRecurrence[{31,31,31,-496}, {1,33, 1056,33792,1080816}, 20] (* _G. C. Greubel_, Dec 11 2016 *)` (wolfram-series)
* `%T coxG[{4, 496, -31}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^4)/(1-32*x+527*x^4-496*x^5)) \\ _G. C. Greubel_, Dec 11 2016, modified Apr 28 2019` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^4)/(1-32*x+527*x^4-496*x^5) )); // _G. C. Greubel_, Apr 28 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163216

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163216 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A163216 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163216
