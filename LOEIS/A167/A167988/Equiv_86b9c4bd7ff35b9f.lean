import LOEIS.A167.A167988.Defs

/-!
# A167988 — program transcriptions (`Equiv_86b9c4bd7ff35b9f`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 1128*t^16 - 47*t^15 - 47*t^14 - 47*t^13 - 47*t^12 - 47*t^11 - 47*t^10 - 47*t^9 - 47*t^8 - 47*t^7 - 47*t^6 - 47*t^5 - 47*t^4 - 47*t^3 - 47*t^2 - 47*t + 1). From _G. C. Greubel_, Jan 14 2023: (Start) a(n) = -1128*a(n-16) + 47*Sum_{j=1..15} a(n-j). G.f.: (1 + x)*(1 - x^16)/(1 - 48*x + 1175*x^16 - 1128*x^17). (End)` (gf-rational)
* `%F a(n) = -1128*a(n-16) + 47*Sum_{j=1..15} a(n-j).` (recurrence)
* `%T coxG[{16,1128,-47}]` (wolfram-coxG)
* `%T CoefficientList[Series[(1+x)*(1-x^16)/(1-48*x+1175*x^16-1128*x^17), {x, 0, 50}], x] (* _G. C. Greubel_, Jul 03 2016; Jan 14 2023 *)` (wolfram-series)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^16)/(1-48*x+1175*x^16-1128*x^17) )); // _G. C. Greubel_, Jan 14 2023` (magma-series)
* `%O (PARI) Vec((1+x^2)*(1+x^4)*(1+x^8)*(1+x)^2/(1-47*x-47*x^2-47*x^3-47*x^4-47*x^5-47*x^6-47*x^7-47*x^8-47*x^9-47*x^10-47*x^11-47*x^12-47*x^13-47*x^14-47*x^15+1128*x^16)+O(x^99)) \\ _Charles R Greathouse IV_, May 16 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167988

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167988 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167988 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167988
