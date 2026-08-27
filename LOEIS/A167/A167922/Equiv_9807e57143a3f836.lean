import LOEIS.A167.A167922.Defs

/-!
# A167922 — program transcriptions (`Equiv_9807e57143a3f836`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 78*t^16 - 12*t^15 - 12*t^14 - 12*t^13 - 12*t^12 - 12*t^11 - 12*t^10 - 12*t^9 - 12*t^8 - 12*t^7 - 12*t^6 - 12*t^5 - 12*t^4 - 12*t^3 - 12*t^2 - 12*t + 1). From _G. C. Greubel_, Sep 13 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 13*t + 90*t^16 - 78*t^17). a(n) = 12*Sum_{j=1..15} a(n-j) - 78*a(n-16). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 78*t^16 - 12*t^15 - 12*t^14 - 12*t^13 - 12*t^12 - 12*t^11 - 12*t^10 - 12*t^9 - 12*t^8 - 12*t^7 - 12*t^6 - 12*t^5 - 12*t^4 - 12*t^3 - 12*t^2 - 12*t + 1). From _G. C. Greubel_, Sep 13 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 13*t + 90*t^16 - 78*t^17). a(n) = 12*Sum_{j=1..15} a(n-j) - 78*a(n-16). (End)` (gf-factored)
* `%F a(n) = 12*Sum_{j=1..15} a(n-j) - 78*a(n-16). (End)` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^16)/(1-13*t+90*t^16-78*t^17), {t, 0, 50}], t] (* _G. C. Greubel_, Jul 01 2016; Sep 13 2023 *)` (wolfram-series)
* `%T coxG[{16, 78, -12, 40}]` (wolfram-coxG)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^16)/(1-13*x+90*x^16-78*x^17) )); // _G. C. Greubel_, Sep 13 2023` (magma-series)
* `%O (PARI) Vec((1+x^2)*(1+x^4)*(1+x^8)*(1+x)^2/(1-12*x-12*x^2-12*x^3-12*x^4-12*x^5-12*x^6-12*x^7-12*x^8-12*x^9-12*x^10-12*x^11-12*x^12-12*x^13-12*x^14-12*x^15+78*x^16)+O(x^99)) \\ _Charles R Greathouse IV_, May 16 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167922

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167922 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167922 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167922
