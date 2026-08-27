import LOEIS.A167.A167980.Defs

/-!
# A167980 — program transcriptions (`Equiv_16915a1c1ee63d90`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 1081*t^16 - 46*t^15 - 46*t^14 - 46*t^13 - 46*t^12 - 46*t^11 - 46*t^10 - 46*t^9 - 46*t^8 - 46*t^7 - 46*t^6 - 46*t^5 - 46*t^4 - 46*t^3 - 46*t^2 - 46*t + 1). From _G. C. Greubel_, Jan 17 2023: (Start) a(n) = Sum_{j=1..15} a(n-j) - 1081*a(n-16). G.f.: (1+x)*(1-x^16)/(1 - 47*x + 1127*x^16 - 1081*x^17). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 1081*t^16 - 46*t^15 - 46*t^14 - 46*t^13 - 46*t^12 - 46*t^11 - 46*t^10 - 46*t^9 - 46*t^8 - 46*t^7 - 46*t^6 - 46*t^5 - 46*t^4 - 46*t^3 - 46*t^2 - 46*t + 1). From _G. C. Greubel_, Jan 17 2023: (Start) a(n) = Sum_{j=1..15} a(n-j) - 1081*a(n-16). G.f.: (1+x)*(1-x^16)/(1 - 47*x + 1127*x^16 - 1081*x^17). (End)` (gf-factored)
* `%F a(n) = Sum_{j=1..15} a(n-j) - 1081*a(n-16).` (recurrence)
* `%T coxG[{16,1081,-46}]` (wolfram-coxG)
* `%T CoefficientList[Series[(1+t)*(1-t^16)/(1-47*t+1127*t^16-1081*t^17), {t, 0,50}], t] (* _G. C. Greubel_, Jul 03 2016; Jan 17 2023 *)` (wolfram-series)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 30); Coefficients(R!( (1+x)*(1-x^16)/(1-47*x+1127*x^16-1081*x^17) )); // _G. C. Greubel_, Jan 17 2023` (magma-series)
* `%O (PARI) Vec((1+x)*(1-x^16)/(1 - 47*x + 1127*x^16 - 1081*x^17)+O(x^30)) \\ _Charles R Greathouse IV_, May 19 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167980

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167980 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167980 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167980
