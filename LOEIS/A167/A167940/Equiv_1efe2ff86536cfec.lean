import LOEIS.A167.A167940.Defs

/-!
# A167940 — program transcriptions (`Equiv_1efe2ff86536cfec`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 276*t^16 - 23*t^15 - 23*t^14 - 23*t^13 - 23*t^12 - 23*t^11 - 23*t^10 - 23*t^9 - 23*t^8 - 23*t^7 - 23*t^6 - 23*t^5 - 23*t^4 - 23*t^3 - 23*t^2 - 23*t + 1). From _G. C. Greubel_, Sep 08 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 24*t + 299*t^16 - 276*t^17). a(n) = 23*Sum_{j=1..15} a(n-j) - 276*a(n-16). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 276*t^16 - 23*t^15 - 23*t^14 - 23*t^13 - 23*t^12 - 23*t^11 - 23*t^10 - 23*t^9 - 23*t^8 - 23*t^7 - 23*t^6 - 23*t^5 - 23*t^4 - 23*t^3 - 23*t^2 - 23*t + 1). From _G. C. Greubel_, Sep 08 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 24*t + 299*t^16 - 276*t^17). a(n) = 23*Sum_{j=1..15} a(n-j) - 276*a(n-16). (End)` (gf-factored)
* `%F a(n) = 23*Sum_{j=1..15} a(n-j) - 276*a(n-16). (End)` (recurrence)
* `%T coxG[{16,276,-23}]` (wolfram-coxG)
* `%T CoefficientList[Series[(1+t)*(1-t^16)/(1-24*t+299*t^16-276*t^17), {t, 0, 50}], t] (* _G. C. Greubel_, Jul 01 2016; Sep 08 2023 *)` (wolfram-series)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^16)/(1-24*x+299*x^16-276*x^17) )); // _G. C. Greubel_, Sep 08 2023` (magma-series)
* `%O (PARI) Vec((x^16+2*x^15+2*x^14+2*x^13+2*x^12+2*x^11+2*x^10+2*x^9+2*x^8+2*x^7+2*x^6+2*x^5+2*x^4+2*x^3+2*x^2+2*x+1)/(276*x^16-23*x^15-23*x^14-23*x^13-23*x^12-23*x^11-23*x^10-23*x^9-23*x^8-23*x^7-23*x^6-23*x^5-23*x^4-23*x^3-23*x^2-23*x+1)+O(x^99)) \\ _Charles R Greathouse IV_, May 15 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167940

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167940 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167940 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167940
