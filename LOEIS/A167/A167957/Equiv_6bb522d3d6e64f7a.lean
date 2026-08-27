import LOEIS.A167.A167957.Defs

/-!
# A167957 — program transcriptions (`Equiv_6bb522d3d6e64f7a`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 780*t^16 - 39*t^15 - 39*t^14 - 39*t^13 - 39*t^12 - 39*t^11 - 39*t^10 - 39*t^9 - 39*t^8 - 39*t^7 - 39*t^6 - 39*t^5 - 39*t^4 - 39*t^3 - 39*t^2 - 39*t + 1). From _G. C. Greubel_, Jul 14 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 -40*t +819*t^16 -780*t^17). a(n) = -780*a(n-16) + 39*Sum_{j=1..15} a(n-j). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 780*t^16 - 39*t^15 - 39*t^14 - 39*t^13 - 39*t^12 - 39*t^11 - 39*t^10 - 39*t^9 - 39*t^8 - 39*t^7 - 39*t^6 - 39*t^5 - 39*t^4 - 39*t^3 - 39*t^2 - 39*t + 1). From _G. C. Greubel_, Jul 14 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 -40*t +819*t^16 -780*t^17). a(n) = -780*a(n-16) + 39*Sum_{j=1..15} a(n-j). (End)` (gf-factored)
* `%F a(n) = -780*a(n-16) + 39*Sum_{j=1..15} a(n-j). (End)` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^16)/(1-40*t+819*t^16-780*t^17), {t, 0, 40}], t] (* _G. C. Greubel_, Jul 02 2016; Jul 14 2023 *)` (wolfram-series)
* `%T coxG[{16,780,-39}]` (wolfram-coxG)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^16)/(1-40*x+819*x^16-780*x^17) )); // _G. C. Greubel_, Jul 14 2023` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167957

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 40

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 40 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167957 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 40).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 40 n h'
  have h2 : A167957 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167957
