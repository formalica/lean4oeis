import LOEIS.A167.A167916.Defs

/-!
# A167916 — program transcriptions (`Equiv_0d35a371fa503521`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 55*t^16 - 10*t^15 - 10*t^14 - 10*t^13 - 10*t^12 - 10*t^11 - 10*t^10 - 10*t^9 - 10*t^8 - 10*t^7 - 10*t^6 - 10*t^5 - 10*t^4 - 10*t^3 - 10*t^2 - 10*t + 1). From _G. C. Greubel_, Nov 10 2023: (Start) a(n) = 10*Sum_{j=1..15} a(n-j) - 55*a(n-16). G.f.: (1+x)*(1-x^16)/(1 - 11*x + 65*x^16 - 55*x^17). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 55*t^16 - 10*t^15 - 10*t^14 - 10*t^13 - 10*t^12 - 10*t^11 - 10*t^10 - 10*t^9 - 10*t^8 - 10*t^7 - 10*t^6 - 10*t^5 - 10*t^4 - 10*t^3 - 10*t^2 - 10*t + 1). From _G. C. Greubel_, Nov 10 2023: (Start) a(n) = 10*Sum_{j=1..15} a(n-j) - 55*a(n-16). G.f.: (1+x)*(1-x^16)/(1 - 11*x + 65*x^16 - 55*x^17). (End)` (gf-factored)
* `%F a(n) = 10*Sum_{j=1..15} a(n-j) - 55*a(n-16).` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^16)/(1-11*t+65*t^16-55*t^17), {t,0,50}], t] (* _G. C. Greubel_, Jul 01 2016; Nov 10 2023 *)` (wolfram-series)
* `%T coxG[{16,55,-10}]` (wolfram-coxG)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 30); Coefficients(R!( (1+x)*(1-x^16)/(1-11*x+65*x^16-55*x^17) )); // _G. C. Greubel_, Nov 10 2023` (magma-series)
* `%O (PARI) Vec((x^16+2*x^15+2*x^14+2*x^13+2*x^12+2*x^11+2*x^10+2*x^9+2*x^8+2*x^7+2*x^6+2*x^5+2*x^4+2*x^3+2*x^2+2*x+1)/(55*x^16-10*x^15-10*x^14-10*x^13-10*x^12-10*x^11-10*x^10-10*x^9-10*x^8-10*x^7-10*x^6-10*x^5-10*x^4-10*x^3-10*x^2-10*x+1)+O(x^99)) \\ _Charles R Greathouse IV_, May 15 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167916

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167916 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A167916 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167916
