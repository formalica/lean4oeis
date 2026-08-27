import LOEIS.A167.A167955.Defs

/-!
# A167955 — program transcriptions (`Equiv_ccfddea55123dcce`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 703*t^16 - 37*t^15 - 37*t^14 - 37*t^13 - 37*t^12 - 37*t^11 - 37*t^10 - 37*t^9 - 37*t^8 - 37*t^7 - 37*t^6 - 37*t^5 - 37*t^4 - 37*t^3 - 37*t^2 - 37*t + 1). From _G. C. Greubel_, Sep 06 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 38*t + 740*t^16 - 703*t^17). a(n) = 37*Sum_{j=1..15} a(n-j) - 703*a(n-16). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 703*t^16 - 37*t^15 - 37*t^14 - 37*t^13 - 37*t^12 - 37*t^11 - 37*t^10 - 37*t^9 - 37*t^8 - 37*t^7 - 37*t^6 - 37*t^5 - 37*t^4 - 37*t^3 - 37*t^2 - 37*t + 1). From _G. C. Greubel_, Sep 06 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 38*t + 740*t^16 - 703*t^17). a(n) = 37*Sum_{j=1..15} a(n-j) - 703*a(n-16). (End)` (gf-factored)
* `%F a(n) = 37*Sum_{j=1..15} a(n-j) - 703*a(n-16). (End)` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^16)/(1-38*t+740*t^16-703*t^17), {t, 0, 50}], t] (* _G. C. Greubel_, Jul 02 2016; Sep 06 2023 *)` (wolfram-series)
* `%T coxG[{16, 703, -37, 40}]` (wolfram-coxG)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^16)/(1-38*x+740*x^16-703*x^17) )); // _G. C. Greubel_, Sep 06 2023` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167955

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167955 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167955 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167955
