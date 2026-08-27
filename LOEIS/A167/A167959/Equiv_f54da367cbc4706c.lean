import LOEIS.A167.A167959.Defs

/-!
# A167959 — program transcriptions (`Equiv_f54da367cbc4706c`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 861*t^16 - 41*t^15 - 41*t^14 - 41*t^13 - 41*t^12 - 41*t^11 - 41*t^10 - 41*t^9 - 41*t^8 - 41*t^7 - 41*t^6 - 41*t^5 - 41*t^4 - 41*t^3 - 41*t^2 - 41*t + 1). From _G. C. Greubel_, Apr 27 2023: (Start) G.f.: (1 + x)*(1 + x^16)/(1 - 42*x + 861*x^16 - 820*x^17). a(n) = 41*Sum_{k=1..15} a(n-k) - 861*a(n-16). (End)` (gf-rational)
* `%F a(n) = 41*Sum_{k=1..15} a(n-k) - 861*a(n-16). (End)` (recurrence)
* `%T CoefficientList[Series[(1+x)*(1+x^16)/(1-42*x+861*x^16-820*x^17), {x, 0, 50}], x] (* _G. C. Greubel_, Jul 02 2016; Apr 27 2023 *)` (wolfram-series)
* `%T coxG[{16, 861, -41, 40}]` (wolfram-coxG)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1+x^16)/(1-42*x+861*x^16-820*x^17) )); // _G. C. Greubel_, Apr 27 2023` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167959

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167959 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167959 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167959
