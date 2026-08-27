import LOEIS.A167.A167937.Defs

/-!
# A167937 — program transcriptions (`Equiv_52ba11d5b3350034`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 231*t^16 - 21*t^15 - 21*t^14 - 21*t^13 - 21*t^12 - 21*t^11 - 21*t^10 - 21*t^9 - 21*t^8 - 21*t^7 - 21*t^6 - 21*t^5 - 21*t^4 - 21*t^3 - 21*t^2 - 21*t + 1). From _G. C. Greubel_, Sep 10 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 22*t + 252*t^16 - 231*t^17). a(n) = 21*Sum_{j=1..15} a(n-j) - 231*a(n-16). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 231*t^16 - 21*t^15 - 21*t^14 - 21*t^13 - 21*t^12 - 21*t^11 - 21*t^10 - 21*t^9 - 21*t^8 - 21*t^7 - 21*t^6 - 21*t^5 - 21*t^4 - 21*t^3 - 21*t^2 - 21*t + 1). From _G. C. Greubel_, Sep 10 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 22*t + 252*t^16 - 231*t^17). a(n) = 21*Sum_{j=1..15} a(n-j) - 231*a(n-16). (End)` (gf-factored)
* `%F a(n) = 21*Sum_{j=1..15} a(n-j) - 231*a(n-16). (End)` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^16)/(1-22*t+252*t^16-231*t^17), {t, 0, 50}], t] (* _G. C. Greubel_, Jul 01 2016; Sep 10 2023 *)` (wolfram-series)
* `%T coxG[{16,231,-21}]` (wolfram-coxG)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^16)/(1-22*x+252*x^16-231*x^17) )); // _G. C. Greubel_, Sep 10 2023` (magma-series)
* `%O (PARI) Vec((1+x^2)*(1+x^4)*(1+x^8)*(1+x)^2/(1-21*x-21*x^2-21*x^3-21*x^4-21*x^5-21*x^6-21*x^7-21*x^8-21*x^9-21*x^10-21*x^11-21*x^12-21*x^13-21*x^14-21*x^15+231*x^16)+O(x^99)) \\ _Charles R Greathouse IV_, May 20 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167937

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167937 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167937 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167937
