import LOEIS.A167.A167954.Defs

/-!
# A167954 — program transcriptions (`Equiv_1f508ae21e487063`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 666*t^16 - 36*t^15 - 36*t^14 - 36*t^13 - 36*t^12 - 36*t^11 - 36*t^10 - 36*t^9 - 36*t^8 - 36*t^7 - 36*t^6 - 36*t^5 - 36*t^4 - 36*t^3 - 36*t^2 - 36*t + 1). From _G. C. Greubel_, Sep 06 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 37*t + 702*t^16 - 666*t^17). a(n) = 36*Sum_{j=1..15} a(n-j) - 666*a(n-16). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 666*t^16 - 36*t^15 - 36*t^14 - 36*t^13 - 36*t^12 - 36*t^11 - 36*t^10 - 36*t^9 - 36*t^8 - 36*t^7 - 36*t^6 - 36*t^5 - 36*t^4 - 36*t^3 - 36*t^2 - 36*t + 1). From _G. C. Greubel_, Sep 06 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 37*t + 702*t^16 - 666*t^17). a(n) = 36*Sum_{j=1..15} a(n-j) - 666*a(n-16). (End)` (gf-factored)
* `%F a(n) = 36*Sum_{j=1..15} a(n-j) - 666*a(n-16). (End)` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^16)/(1-37*t+702*t^16-666*t^17), {t, 0, 50}], t] (* _G. C. Greubel_, Jul 02 2016 *)` (wolfram-series)
* `%T coxG[{16, 666, -36, 40}]` (wolfram-coxG)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^16)/(1-37*x+702*x^16-666*x^17) )); // _G. C. Greubel_, Sep 06 2023` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167954

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167954 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167954 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167954
