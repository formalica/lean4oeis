import LOEIS.A167.A167938.Defs

/-!
# A167938 — program transcriptions (`Equiv_4a47c64b90fd8d2d`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 253*t^16 - 22*t^15 - 22*t^14 - 22*t^13 - 22*t^12 - 22*t^11 - 22*t^10 - 22*t^9 - 22*t^8 - 22*t^7 - 22*t^6 - 22*t^5 - 22*t^4 - 22*t^3 - 22*t^2 - 22*t + 1). From _G. C. Greubel_, Sep 09 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 23*t + 275*t^16 - 253*t^17). a(n) = 22*Sum_{j=1..15} a(n-j) - 253*a(n-16). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 253*t^16 - 22*t^15 - 22*t^14 - 22*t^13 - 22*t^12 - 22*t^11 - 22*t^10 - 22*t^9 - 22*t^8 - 22*t^7 - 22*t^6 - 22*t^5 - 22*t^4 - 22*t^3 - 22*t^2 - 22*t + 1). From _G. C. Greubel_, Sep 09 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 23*t + 275*t^16 - 253*t^17). a(n) = 22*Sum_{j=1..15} a(n-j) - 253*a(n-16). (End)` (gf-factored)
* `%F a(n) = 22*Sum_{j=1..15} a(n-j) - 253*a(n-16). (End)` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^16)/(1-23*t+275*t^16-253*t^17), {t, 0, 50}], t] (* _G. C. Greubel_, Jul 01 2016; Sep 09 2023 *)` (wolfram-series)
* `%T coxG[{16,253,-22}]` (wolfram-coxG)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^16)/(1-23*x+275*x^16-253*x^17) )); // _G. C. Greubel_, Sep 09 2023` (magma-series)
* `%O (PARI) Vec((x^16+2*x^15+2*x^14+2*x^13+2*x^12+2*x^11+2*x^10+2*x^9+2*x^8+2*x^7+2*x^6+2*x^5+2*x^4+2*x^3+2*x^2+2*x+1)/(253*x^16-22*x^15-22*x^14-22*x^13-22*x^12-22*x^11-22*x^10-22*x^9-22*x^8-22*x^7-22*x^6-22*x^5-22*x^4-22*x^3-22*x^2-22*x+1)+O(x^99)) \\ _Charles R Greathouse IV_, May 15 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167938

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167938 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167938 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167938
