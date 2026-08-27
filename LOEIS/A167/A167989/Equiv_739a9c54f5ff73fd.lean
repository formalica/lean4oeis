import LOEIS.A167.A167989.Defs

/-!
# A167989 — program transcriptions (`Equiv_739a9c54f5ff73fd`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 1176*t^16 - 48*t^15 - 48*t^14 - 48*t^13 - 48*t^12 - 48*t^11 - 48*t^10 - 48*t^9 - 48*t^8 - 48*t^7 - 48*t^6 - 48*t^5 - 48*t^4 - 48*t^3 - 48*t^2 - 48*t + 1). From _G. C. Greubel_, Jan 14 2023: (Start) a(n) = -1176*a(n-16) + 48*Sum_{j=1..15} a(n-j). G.f.: (1+x)*(1-x^16)/(1-49*x+1224*x^16-1176*x^17). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 1176*t^16 - 48*t^15 - 48*t^14 - 48*t^13 - 48*t^12 - 48*t^11 - 48*t^10 - 48*t^9 - 48*t^8 - 48*t^7 - 48*t^6 - 48*t^5 - 48*t^4 - 48*t^3 - 48*t^2 - 48*t + 1). From _G. C. Greubel_, Jan 14 2023: (Start) a(n) = -1176*a(n-16) + 48*Sum_{j=1..15} a(n-j). G.f.: (1+x)*(1-x^16)/(1-49*x+1224*x^16-1176*x^17). (End)` (gf-factored)
* `%F a(n) = -1176*a(n-16) + 48*Sum_{j=1..15} a(n-j).` (recurrence)
* `%T CoefficientList[Series[(1+x)*(1-x^16)/(1-49*x+1224*x^16-1176*x^17), {x, 0, 50}], x] (* _G. C. Greubel_, Jul 03 2016; Jan 14 2023 *)` (wolfram-series)
* `%T coxG[{16, 1176, -48, 10}]` (wolfram-coxG)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^16)/(1-49*x+1224*x^16-1176*x^17) )); // _G. C. Greubel_, Jan 14 2023` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167989

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167989 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167989 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167989
