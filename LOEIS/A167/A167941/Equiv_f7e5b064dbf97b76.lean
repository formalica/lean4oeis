import LOEIS.A167.A167941.Defs

/-!
# A167941 — program transcriptions (`Equiv_f7e5b064dbf97b76`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 300*t^16 - 24*t^15 - 24*t^14 - 24*t^13 - 24*t^12 - 24*t^11 - 24*t^10 - 24*t^9 - 24*t^8 - 24*t^7 - 24*t^6 - 24*t^5 - 24*t^4 - 24*t^3 - 24*t^2 - 24*t + 1). From _G. C. Greubel_, Sep 08 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 25*t + 324*t^16 - 300*t^17). a(n) = 24*Sum_{j=1..15} a(n-j) - 300*a(n-16). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 300*t^16 - 24*t^15 - 24*t^14 - 24*t^13 - 24*t^12 - 24*t^11 - 24*t^10 - 24*t^9 - 24*t^8 - 24*t^7 - 24*t^6 - 24*t^5 - 24*t^4 - 24*t^3 - 24*t^2 - 24*t + 1). From _G. C. Greubel_, Sep 08 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 25*t + 324*t^16 - 300*t^17). a(n) = 24*Sum_{j=1..15} a(n-j) - 300*a(n-16). (End)` (gf-factored)
* `%F a(n) = 24*Sum_{j=1..15} a(n-j) - 300*a(n-16). (End)` (recurrence)
* `%T coxG[{16,300,-24}]` (wolfram-coxG)
* `%T CoefficientList[Series[(1+t)*(1-t^16)/(1-25*t+324*t^16-300*t^17), {t, 0, 50}], t] (* _G. C. Greubel_, Sep 08 2023 *)` (wolfram-series)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^16)/(1-25*x+324*x^16-300*x^17) )); // _G. C. Greubel_, Sep 08 2023` (magma-series)
* `%O (PARI) first(n)=Vec((1+x^8)*(1+x^4)*(1+x^2)*(1+x)^2/(1-24*x-24*x^2-24*x^3-24*x^4-24*x^5-24*x^6-24*x^7-24*x^8-24*x^9-24*x^10-24*x^11-24*x^12-24*x^13-24*x^14-24*x^15+300*x^16)+O(x^(n+1))) \\ _Charles R Greathouse IV_, Aug 14 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167941

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167941 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167941 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167941
