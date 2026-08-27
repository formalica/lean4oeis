import LOEIS.A167.A167958.Defs

/-!
# A167958 — program transcriptions (`Equiv_3ae9f654afe6cf70`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 820*t^16 - 40*t^15 - 40*t^14 - 40*t^13 - 40*t^12 - 40*t^11 - 40*t^10 - 40*t^9 - 40*t^8 - 40*t^7 - 40*t^6 - 40*t^5 - 40*t^4 - 40*t^3 - 40*t^2 - 40*t + 1). From _G. C. Greubel_, Jul 14 2023: (Start) G.f.: (1 + t)*(1 - t^16)/(1 - 41*t + 860*t^16 - 820*t^17). a(n) = -820*a(n-16) + 40*Sum_{j=1..15} a(n-j). (End)` (gf-rational)
* `%F a(n) = -820*a(n-16) + 40*Sum_{j=1..15} a(n-j). (End)` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^16)/(1-41*t+860*t^16 -820*t^17), {t, 0, 40}], t] (* _G. C. Greubel_, Jul 02 2016; Jul 14 2023 *)` (wolfram-series)
* `%T coxG[{16, 820, -40, 30}]` (wolfram-coxG)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^16)/(1-41*x+860*x^16-820*x^17) )); // _G. C. Greubel_, Jul 14 2023` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167958

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 40

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 40 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167958 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 40).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 40 n h'
  have h2 : A167958 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167958
