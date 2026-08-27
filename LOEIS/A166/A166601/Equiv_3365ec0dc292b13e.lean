import LOEIS.A166.A166601.Defs

/-!
# A166601 — program transcriptions (`Equiv_3365ec0dc292b13e`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(171*t^12 - 18*t^11 - 18*t^10 - 18*t^9 -18*t^8 -18*t^7 - 18*t^6 - 18*t^5 - 18*t^4 - 18*t^3 - 18*t^2 -18*t + 1). From _G. C. Greubel_, Dec 30 2024: (Start) a(n) = 18*Sum_{j=1..11} a(n-j) - 171*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 19*x + 189*x^12 - 171*x^13). (End)` (gf-rational)
* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(171*t^12 - 18*t^11 - 18*t^10 - 18*t^9 -18*t^8 -18*t^7 - 18*t^6 - 18*t^5 - 18*t^4 - 18*t^3 - 18*t^2 -18*t + 1). From _G. C. Greubel_, Dec 30 2024: (Start) a(n) = 18*Sum_{j=1..11} a(n-j) - 171*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 19*x + 189*x^12 - 171*x^13). (End)` (gf-factored)
* `%F a(n) = 18*Sum_{j=1..11} a(n-j) - 171*a(n-12).` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^12)/(1-19*t+189*t^12-171*t^13), {t,0,50}], t] (* _G. C. Greubel_, May 18 2016; Dec 30 2024 *)` (wolfram-series)
* `%T coxG[{12,171,-18}]` (wolfram-coxG)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 50); Coefficients(R!( (1+x)*(1-x^12)/(1-19*x+189*x^12-171*x^13) )); // _G. C. Greubel_, Dec 30 2024` (magma-series)
* `%O (PARI) Vec((1+x^4+x^8)*(1+x^2)*(1+x)^2/(1-18*x-18*x^2-18*x^3-18*x^4-18*x^5-18*x^6-18*x^7-18*x^8-18*x^9-18*x^10-18*x^11+171*x^12)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166601

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166601 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166601 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166601
