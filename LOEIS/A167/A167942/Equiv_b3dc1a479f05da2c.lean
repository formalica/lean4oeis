import LOEIS.A167.A167942.Defs

/-!
# A167942 — program transcriptions (`Equiv_b3dc1a479f05da2c`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 325*t^16 - 25*t^15 - 25*t^14 - 25*t^13 - 25*t^12 - 25*t^11 - 25*t^10 - 25*t^9 - 25*t^8 - 25*t^7 - 25*t^6 - 25*t^5 - 25*t^4 - 25*t^3 - 25*t^2 - 25*t + 1). From _G. C. Greubel_, Sep 08 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 26*t + 350*t^16 - 325*t^17). a(n) = 25*Sum_{j=1..15} a(n-j) - 325*a(n-16). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 325*t^16 - 25*t^15 - 25*t^14 - 25*t^13 - 25*t^12 - 25*t^11 - 25*t^10 - 25*t^9 - 25*t^8 - 25*t^7 - 25*t^6 - 25*t^5 - 25*t^4 - 25*t^3 - 25*t^2 - 25*t + 1). From _G. C. Greubel_, Sep 08 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 26*t + 350*t^16 - 325*t^17). a(n) = 25*Sum_{j=1..15} a(n-j) - 325*a(n-16). (End)` (gf-factored)
* `%F a(n) = 25*Sum_{j=1..15} a(n-j) - 325*a(n-16). (End)` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^16)/(1-26*t+350*t^16-325*t^17), {t, 0, 50}], t] (* _G. C. Greubel_, Jul 01 2016; Sep 08 2023 *)` (wolfram-series)
* `%T coxG[{16,325,-25}]` (wolfram-coxG)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^16)/(1-26*x+350*x^16-325*x^17) )); // _G. C. Greubel_, Sep 08 2023` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167942

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167942 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167942 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167942
