import LOEIS.A167.A167919.Defs

/-!
# A167919 — program transcriptions (`Equiv_b5d40f36414c7fe7`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 66*t^16 - 11*t^15 - 11*t^14 - 11*t^13 - 11*t^12 - 11*t^11 - 11*t^10 - 11*t^9 - 11*t^8 - 11*t^7 - 11*t^6 - 11*t^5 - 11*t^4 - 11*t^3 - 11*t^2 - 11*t + 1). From _G. C. Greubel_, Sep 13 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 12*t + 77*t^16 - 66*t^17). a(n) = 11*Sum_{j=1..15} a(n-j) - 66*a(n-16). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 66*t^16 - 11*t^15 - 11*t^14 - 11*t^13 - 11*t^12 - 11*t^11 - 11*t^10 - 11*t^9 - 11*t^8 - 11*t^7 - 11*t^6 - 11*t^5 - 11*t^4 - 11*t^3 - 11*t^2 - 11*t + 1). From _G. C. Greubel_, Sep 13 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 12*t + 77*t^16 - 66*t^17). a(n) = 11*Sum_{j=1..15} a(n-j) - 66*a(n-16). (End)` (gf-factored)
* `%F a(n) = 11*Sum_{j=1..15} a(n-j) - 66*a(n-16). (End)` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^16)/(1-12*t+77*t^16-66*t^17), {t, 0, 50}], t] (* _G. C. Greubel_, Jul 01 2016; Sep 13 2023 *)` (wolfram-series)
* `%T coxG[{16,66,-11}]` (wolfram-coxG)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^16)/(1-12*x+77*x^16-66*x^17) )); // _G. C. Greubel_, Sep 13 2023` (magma-series)
* `%O (PARI) Vec((1+x^2)*(1+x^4)*(1+x^8)*(1+x)^2/(1-11*x-11*x^2-11*x^3-11*x^4-11*x^5-11*x^6-11*x^7-11*x^8-11*x^9-11*x^10-11*x^11-11*x^12-11*x^13-11*x^14-11*x^15+66*x^16)+O(x^99)) \\ _Charles R Greathouse IV_, May 16 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167919

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167919 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167919 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167919
