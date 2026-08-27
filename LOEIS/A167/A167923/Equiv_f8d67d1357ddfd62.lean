import LOEIS.A167.A167923.Defs

/-!
# A167923 — program transcriptions (`Equiv_f8d67d1357ddfd62`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 91*t^16 - 13*t^15 - 13*t^14 - 13*t^13 - 13*t^12 - 13*t^11 - 13*t^10 - 13*t^9 - 13*t^8 - 13*t^7 - 13*t^6 - 13*t^5 - 13*t^4 - 13*t^3 - 13*t^2 - 13*t + 1). From _G. C. Greubel_, Sep 10 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 14*t + 104*t^16 - 91*t^17). a(n) = 13*Sum_{j=1..15} a(n-j) - 91*a(n-16). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 91*t^16 - 13*t^15 - 13*t^14 - 13*t^13 - 13*t^12 - 13*t^11 - 13*t^10 - 13*t^9 - 13*t^8 - 13*t^7 - 13*t^6 - 13*t^5 - 13*t^4 - 13*t^3 - 13*t^2 - 13*t + 1). From _G. C. Greubel_, Sep 10 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 14*t + 104*t^16 - 91*t^17). a(n) = 13*Sum_{j=1..15} a(n-j) - 91*a(n-16). (End)` (gf-factored)
* `%F a(n) = 13*Sum_{j=1..15} a(n-j) - 91*a(n-16). (End)` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^16)/(1-14*t+104*t^16-91*t^17), {t, 0, 50}], t] (* _G. C. Greubel_, Jul 01 2016; Sep 10 2023 *)` (wolfram-series)
* `%T coxG[{16,91,-13}]` (wolfram-coxG)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^16)/(1-14*x+104*x^16-91*x^17) )); // _G. C. Greubel_, Sep 10 2023` (magma-series)
* `%O (PARI) Vec((x^16+2*x^15+2*x^14+2*x^13+2*x^12+2*x^11+2*x^10+2*x^9+2*x^8+2*x^7+2*x^6+2*x^5+2*x^4+2*x^3+2*x^2+2*x+1)/(91*x^16-13*x^15-13*x^14-13*x^13-13*x^12-13*x^11-13*x^10-13*x^9-13*x^8-13*x^7-13*x^6-13*x^5-13*x^4-13*x^3-13*x^2-13*x+1)+O(x^99)) \\ _Charles R Greathouse IV_, May 15 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167923

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167923 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167923 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167923
