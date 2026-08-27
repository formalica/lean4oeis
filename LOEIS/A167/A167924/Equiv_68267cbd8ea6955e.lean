import LOEIS.A167.A167924.Defs

/-!
# A167924 — program transcriptions (`Equiv_68267cbd8ea6955e`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 105*t^16 - 14*t^15 - 14*t^14 - 14*t^13 - 14*t^12 - 14*t^11 - 14*t^10 - 14*t^9 - 14*t^8 - 14*t^7 - 14*t^6 - 14*t^5 - 14*t^4 - 14*t^3 - 14*t^2 - 14*t + 1). From _G. C. Greubel_, Sep 10 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 15*t + 119*t^16 - 105*t^17). a(n) = 14*Sum_{j=1..15} a(n-j) - 105*a(n-16). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 105*t^16 - 14*t^15 - 14*t^14 - 14*t^13 - 14*t^12 - 14*t^11 - 14*t^10 - 14*t^9 - 14*t^8 - 14*t^7 - 14*t^6 - 14*t^5 - 14*t^4 - 14*t^3 - 14*t^2 - 14*t + 1). From _G. C. Greubel_, Sep 10 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 15*t + 119*t^16 - 105*t^17). a(n) = 14*Sum_{j=1..15} a(n-j) - 105*a(n-16). (End)` (gf-factored)
* `%F a(n) = 14*Sum_{j=1..15} a(n-j) - 105*a(n-16). (End)` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^16)/(1-15*t+119*t^16-105*t^17), {t, 0, 50}], t] (* _G. C. Greubel_, Jul 01 2016; Sep 10 2023 *)` (wolfram-series)
* `%T coxG[{16,105,-14}]` (wolfram-coxG)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^16)/(1-15*x+119*x^16-105*x^17) )); // _G. C. Greubel_, Sep 10 2023` (magma-series)
* `%O (PARI) Vec((x^16+2*x^15+2*x^14+2*x^13+2*x^12+2*x^11+2*x^10+2*x^9+2*x^8+2*x^7+2*x^6+2*x^5+2*x^4+2*x^3+2*x^2+2*x+1)/(105*x^16-14*x^15-14*x^14-14*x^13-14*x^12-14*x^11-14*x^10-14*x^9-14*x^8-14*x^7-14*x^6-14*x^5-14*x^4-14*x^3-14*x^2-14*x+1)+O(x^99)) \\ _Charles R Greathouse IV_, May 15 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167924

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167924 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167924 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167924
