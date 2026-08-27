import LOEIS.A167.A167882.Defs

/-!
# A167882 — program transcriptions (`Equiv_ad9946f2f31a065d`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1) / ( 3*t^16 - 2*t^15 - 2*t^14 - 2*t^13 - 2*t^12 - 2*t^11 - 2*t^10 - 2*t^9 - 2*t^8 - 2*t^7 - 2*t^6 - 2*t^5 - 2*t^4 - 2*t^3 - 2*t^2 - 2*t + 1). From _G. C. Greubel_, Jan 17 2023: (Start) a(n) = 2*Sum_{j=1..15} a(n-j) - 3*a(n-16). G.f.: (1+x)*(1-x^16)/(1 - 3*x + 5*x^16 - 3*x^17). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1) / ( 3*t^16 - 2*t^15 - 2*t^14 - 2*t^13 - 2*t^12 - 2*t^11 - 2*t^10 - 2*t^9 - 2*t^8 - 2*t^7 - 2*t^6 - 2*t^5 - 2*t^4 - 2*t^3 - 2*t^2 - 2*t + 1). From _G. C. Greubel_, Jan 17 2023: (Start) a(n) = 2*Sum_{j=1..15} a(n-j) - 3*a(n-16). G.f.: (1+x)*(1-x^16)/(1 - 3*x + 5*x^16 - 3*x^17). (End)` (gf-factored)
* `%F a(n) = 2*Sum_{j=1..15} a(n-j) - 3*a(n-16).` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^16)/(1-3*t+5*t^16-3*t^17), {t,0,50}], t] (* _G. C. Greubel_, Jun 29 2016; Dec 06 2024 *)` (wolfram-series)
* `%T coxG[{16,3,-2}]` (wolfram-coxG)
* `%O R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^16)/(1-3*x+5*x^16-3*x^17) )); // _G. C. Greubel_, Dec 06 2024` (magma-series)
* `%O (PARI) Vec((x^16+2*x^15+2*x^14+2*x^13+2*x^12+2*x^11+2*x^10+2*x^9+2*x^8+2*x^7+2*x^6+2*x^5+2*x^4+2*x^3+2*x^2+2*x+1)/(3*x^16-2*x^15-2*x^14-2*x^13-2*x^12-2*x^11-2*x^10-2*x^9-2*x^8-2*x^7-2*x^6-2*x^5-2*x^4-2*x^3-2*x^2-2*x+1)+O(x^99)) \\ _Charles R Greathouse IV_, May 15 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167882

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167882 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A167882 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167882
