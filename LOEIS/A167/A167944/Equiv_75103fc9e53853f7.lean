import LOEIS.A167.A167944.Defs

/-!
# A167944 — program transcriptions (`Equiv_75103fc9e53853f7`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 378*t^16 - 27*t^15 - 27*t^14 - 27*t^13 - 27*t^12 - 27*t^11 - 27*t^10 - 27*t^9 - 27*t^8 - 27*t^7 - 27*t^6 - 27*t^5 - 27*t^4 - 27*t^3 - 27*t^2 - 27*t + 1). From _G. C. Greubel_, Sep 07 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 28*t + 405*t^16 - 378*t^17). a(n) = 27*Sum_{j=1..15} a(n-j) - 378*a(n-16). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 378*t^16 - 27*t^15 - 27*t^14 - 27*t^13 - 27*t^12 - 27*t^11 - 27*t^10 - 27*t^9 - 27*t^8 - 27*t^7 - 27*t^6 - 27*t^5 - 27*t^4 - 27*t^3 - 27*t^2 - 27*t + 1). From _G. C. Greubel_, Sep 07 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 28*t + 405*t^16 - 378*t^17). a(n) = 27*Sum_{j=1..15} a(n-j) - 378*a(n-16). (End)` (gf-factored)
* `%F a(n) = 27*Sum_{j=1..15} a(n-j) - 378*a(n-16). (End)` (recurrence)
* `%T coxG[{16,378,-27}]` (wolfram-coxG)
* `%T CoefficientList[Series[(1+t)*(1-t^16)/(1-28*t+405*t^16-378*t^17), {t, 0, 50}], t] (* _G. C. Greubel_, Jul 02 2016; Sep 07 2023 *)` (wolfram-series)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^16)/(1-28*x+405*x^16-378*x^17) )); // _G. C. Greubel_, Sep 07 2023` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167944

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167944 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167944 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167944
