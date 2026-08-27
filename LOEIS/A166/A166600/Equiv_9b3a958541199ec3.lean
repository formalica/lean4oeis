import LOEIS.A166.A166600.Defs

/-!
# A166600 — program transcriptions (`Equiv_9b3a958541199ec3`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(153*t^12 - 17*t^11 - 17*t^10 - 17*t^9 -17*t^8 -17*t^7 - 17*t^6 - 17*t^5 - 17*t^4 - 17*t^3 - 17*t^2 -17*t + 1). From _G. C. Greubel_, Dec 08 2024: (Start) a(n) = 17*Sum_{j=1..11} a(n-j) - 153*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 18*x + 170*x^12 - 153*x^13). (End)` (gf-rational)
* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(153*t^12 - 17*t^11 - 17*t^10 - 17*t^9 -17*t^8 -17*t^7 - 17*t^6 - 17*t^5 - 17*t^4 - 17*t^3 - 17*t^2 -17*t + 1). From _G. C. Greubel_, Dec 08 2024: (Start) a(n) = 17*Sum_{j=1..11} a(n-j) - 153*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 18*x + 170*x^12 - 153*x^13). (End)` (gf-factored)
* `%F a(n) = 17*Sum_{j=1..11} a(n-j) - 153*a(n-12).` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^12)/(1-18*t+170*t^12-153*t^13), {t, 0, 50}], t] (* _G. C. Greubel_, May 18 2016; Dec 08 2024 *)` (wolfram-series)
* `%T coxG[{12,153,-17}]` (wolfram-coxG)
* `%O R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^12)/(1 - 18*x+170*x^12-153*x^13) )); // _G. C. Greubel_, Dec 08 2024` (magma-series)
* `%O (PARI) Vec((1+x^4+x^8)*(1+x^2)*(1+x)^2/(1-17*x-17*x^2-17*x^3-17*x^4-17*x^5-17*x^6-17*x^7-17*x^8-17*x^9-17*x^10-17*x^11+153*x^12)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166600

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166600 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A166600 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166600
