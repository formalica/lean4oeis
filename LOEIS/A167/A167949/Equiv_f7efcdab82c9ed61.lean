import LOEIS.A167.A167949.Defs

/-!
# A167949 — program transcriptions (`Equiv_f7efcdab82c9ed61`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 496*t^16 - 31*t^15 - 31*t^14 - 31*t^13 - 31*t^12 - 31*t^11 - 31*t^10 - 31*t^9 - 31*t^8 - 31*t^7 - 31*t^6 - 31*t^5 - 31*t^4 - 31*t^3 - 31*t^2 - 31*t + 1). From _G. C. Greubel_, Sep 07 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 32*t + 527*t^16 - 496*t^17). a(n) = 31*Sum_{j=1..15} a(n-j) - 496*a(n-16). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 496*t^16 - 31*t^15 - 31*t^14 - 31*t^13 - 31*t^12 - 31*t^11 - 31*t^10 - 31*t^9 - 31*t^8 - 31*t^7 - 31*t^6 - 31*t^5 - 31*t^4 - 31*t^3 - 31*t^2 - 31*t + 1). From _G. C. Greubel_, Sep 07 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 32*t + 527*t^16 - 496*t^17). a(n) = 31*Sum_{j=1..15} a(n-j) - 496*a(n-16). (End)` (gf-factored)
* `%F a(n) = 31*Sum_{j=1..15} a(n-j) - 496*a(n-16). (End)` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^16)/(1-32*t+527*t^16-496*t^17), {t, 0, 50}], t] (* _G. C. Greubel_, Jul 02 2016; Sep 07 2023 *)` (wolfram-series)
* `%T coxG[{16,496,-31}]` (wolfram-coxG)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^16)/(1-32*x+527*x^16-496*x^17) )); // _G. C. Greubel_, Sep 07 2023` (magma-series)
* `%O (PARI) Vec((1+x)*(1-x^16)/(1 - 32*x + 527*x^16 - 496*x^17)+O(x^40)) \\ _Charles R Greathouse IV_, May 18 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167949

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167949 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167949 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167949
