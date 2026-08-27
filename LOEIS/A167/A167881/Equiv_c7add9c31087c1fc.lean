import LOEIS.A167.A167881.Defs

/-!
# A167881 — program transcriptions (`Equiv_c7add9c31087c1fc`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(t^16 - t^15 - t^14 - t^13 - t^12 - t^11 - t^10 - t^9 - t^8 - t^7 - t^6 - t^5 - t^4 - t^3 - t^2 - t + 1). From _G. C. Greubel_, Dec 06 2024: (Start) a(n) = Sum_{j=1..15} a(n-j) - a(n-16). G.f.: (1+x)*(1-x^16)/(1 - 2*x + 2*x^16 - x^17). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(t^16 - t^15 - t^14 - t^13 - t^12 - t^11 - t^10 - t^9 - t^8 - t^7 - t^6 - t^5 - t^4 - t^3 - t^2 - t + 1). From _G. C. Greubel_, Dec 06 2024: (Start) a(n) = Sum_{j=1..15} a(n-j) - a(n-16). G.f.: (1+x)*(1-x^16)/(1 - 2*x + 2*x^16 - x^17). (End)` (gf-factored)
* `%F a(n) = Sum_{j=1..15} a(n-j) - a(n-16).` (recurrence)
* `%T CoefficientList[Series[(1+x)*(1-x^16)/(1-2*x+2*x^16-x^17), {x,0,50}], x] (* _G. C. Greubel_, Jun 29 2016; Dec 06 2024 *)` (wolfram-series)
* `%T coxG[{16,1,-1}]` (wolfram-coxG)
* `%O R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^16)/(1-2*x+2*x^16-x^17) )); // _G. C. Greubel_, Dec 06 2024` (magma-series)
* `%O (PARI) Vec((x^16+2*x^15+2*x^14+2*x^13+2*x^12+2*x^11+2*x^10+2*x^9+2*x^8+2*x^7+2*x^6+2*x^5+2*x^4+2*x^3+2*x^2+2*x+1)/(x^16-x^15-x^14-x^13-x^12-x^11-x^10-x^9-x^8-x^7-x^6-x^5-x^4-x^3-x^2-x+1)+O(x^99)) \\ _Charles R Greathouse IV_, May 13 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167881

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167881 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A167881 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167881
