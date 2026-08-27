import LOEIS.A167.A167962.Defs

/-!
# A167962 — program transcriptions (`Equiv_9709ab5feb04cd83`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 990*t^16 - 44*t^15 - 44*t^14 - 44*t^13 - 44*t^12 - 44*t^11 - 44*t^10 - 44*t^9 - 44*t^8 - 44*t^7 - 44*t^6 - 44*t^5 - 44*t^4 - 44*t^3 - 44*t^2 - 44*t + 1). From _G. C. Greubel_, Jan 17 2023: (Start) a(n) = Sum_{j=1..15} a(n-j) - 990*a(n-16). G.f.: (1+x)*(1-x^16)/(1 - 45*x + 1034*x^16 - 990*x^17). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 990*t^16 - 44*t^15 - 44*t^14 - 44*t^13 - 44*t^12 - 44*t^11 - 44*t^10 - 44*t^9 - 44*t^8 - 44*t^7 - 44*t^6 - 44*t^5 - 44*t^4 - 44*t^3 - 44*t^2 - 44*t + 1). From _G. C. Greubel_, Jan 17 2023: (Start) a(n) = Sum_{j=1..15} a(n-j) - 990*a(n-16). G.f.: (1+x)*(1-x^16)/(1 - 45*x + 1034*x^16 - 990*x^17). (End)` (gf-factored)
* `%F a(n) = Sum_{j=1..15} a(n-j) - 990*a(n-16).` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^16)/(1-45*t+1034*t^16-990*t^17), {t, 0, 50}], t] (* _G. C. Greubel_, Jul 03 2016 *)` (wolfram-series)
* `%T coxG[{16,990,-44,40}]` (wolfram-coxG)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^16)/(1-45*x+1034*x^16-990*x^17) )); // _G. C. Greubel_, Jan 17 2023` (magma-series)
* `%O (PARI) Vec((1+x^2)*(1+x^4)*(1+x^8)*(1+x)^2/(1-44*x-44*x^2-44*x^3-44*x^4-44*x^5-44*x^6-44*x^7-44*x^8-44*x^9-44*x^10-44*x^11-44*x^12-44*x^13-44*x^14-44*x^15+990*x^16)+O(x^99)) \\ _Charles R Greathouse IV_, May 18 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167962

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167962 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167962 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167962
