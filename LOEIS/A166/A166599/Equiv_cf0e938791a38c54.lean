import LOEIS.A166.A166599.Defs

/-!
# A166599 — program transcriptions (`Equiv_cf0e938791a38c54`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(136*t^12 - 16*t^11 - 16*t^10 - 16*t^9 -16*t^8 - 16*t^7 - 16*t^6 - 16*t^5 - 16*t^4 - 16*t^3 - 16*t^2 -16*t +1). From _G. C. Greubel_, Dec 08 2024: (Start) a(n) = 16*Sum_{j=1..11} a(n-j) - 136*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 17*x + 152*x^12 - 136*x^13). (End)` (gf-rational)
* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(136*t^12 - 16*t^11 - 16*t^10 - 16*t^9 -16*t^8 - 16*t^7 - 16*t^6 - 16*t^5 - 16*t^4 - 16*t^3 - 16*t^2 -16*t +1). From _G. C. Greubel_, Dec 08 2024: (Start) a(n) = 16*Sum_{j=1..11} a(n-j) - 136*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 17*x + 152*x^12 - 136*x^13). (End)` (gf-factored)
* `%F a(n) = 16*Sum_{j=1..11} a(n-j) - 136*a(n-12).` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^12)/(1-17*t+152*t^12-136*t^13), {t,0,50}], t] (* _G. C. Greubel_, May 18 2016; Dec 08 2024 *)` (wolfram-series)
* `%T coxG[{12,136,-16,40}]` (wolfram-coxG)
* `%O R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^12)/(1 - 17*x+152*x^12-136*x^13) )); // _G. C. Greubel_, Dec 08 2024` (magma-series)
* `%O (PARI) Vec((1+x^4+x^8)*(1+x^2)*(1+x)^2/(1-16*x-16*x^2-16*x^3-16*x^4-16*x^5-16*x^6-16*x^7-16*x^8-16*x^9-16*x^10-16*x^11+136*x^12)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166599

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166599 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166599 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166599
