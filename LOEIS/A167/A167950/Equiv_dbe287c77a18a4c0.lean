import LOEIS.A167.A167950.Defs

/-!
# A167950 — program transcriptions (`Equiv_dbe287c77a18a4c0`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 528*t^16 - 32*t^15 - 32*t^14 - 32*t^13 - 32*t^12 - 32*t^11 - 32*t^10 - 32*t^9 - 32*t^8 - 32*t^7 - 32*t^6 - 32*t^5 - 32*t^4 - 32*t^3 - 32*t^2 - 32*t + 1). From _G. C. Greubel_, Sep 06 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 33*t + 560*t^16 - 528*t^17). a(n) = 32*Sum_{j=1..15} a(n-j) - 528*a(n-16). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 528*t^16 - 32*t^15 - 32*t^14 - 32*t^13 - 32*t^12 - 32*t^11 - 32*t^10 - 32*t^9 - 32*t^8 - 32*t^7 - 32*t^6 - 32*t^5 - 32*t^4 - 32*t^3 - 32*t^2 - 32*t + 1). From _G. C. Greubel_, Sep 06 2023: (Start) G.f.: (1+t)*(1-t^16)/(1 - 33*t + 560*t^16 - 528*t^17). a(n) = 32*Sum_{j=1..15} a(n-j) - 528*a(n-16). (End)` (gf-factored)
* `%F a(n) = 32*Sum_{j=1..15} a(n-j) - 528*a(n-16). (End)` (recurrence)
* `%T coxG[{16,528,-32}]` (wolfram-coxG)
* `%T CoefficientList[Series[(1+t)*(1-t^16)/(1-33*t+560*t^16-528*t^17), {t, 0, 50}], t] (* _G. C. Greubel_, Jul 02 2016; Sep 06 2023 *)` (wolfram-series)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^16)/(1-33*x+560*x^16-528*x^17) )); // _G. C. Greubel_, Sep 06 2023` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167950

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167950 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167950 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167950
