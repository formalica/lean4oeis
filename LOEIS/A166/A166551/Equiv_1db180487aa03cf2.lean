import LOEIS.A166.A166551.Defs

/-!
# A166551 — program transcriptions (`Equiv_1db180487aa03cf2`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(45*t^12 - 9*t^11 - 9*t^10 - 9*t^9 - 9*t^8 - 9*t^7 - 9*t^6 - 9*t^5 - 9*t^4 - 9*t^3 - 9*t^2 - 9*t + 1). From _G. C. Greubel_, Aug 23 2024: (Start) a(n) = 9*Sum_{j=1..11} a(n-j) - 45*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 10*x + 54*x^12 - 45*x^13). (End)` (gf-rational)
* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(45*t^12 - 9*t^11 - 9*t^10 - 9*t^9 - 9*t^8 - 9*t^7 - 9*t^6 - 9*t^5 - 9*t^4 - 9*t^3 - 9*t^2 - 9*t + 1). From _G. C. Greubel_, Aug 23 2024: (Start) a(n) = 9*Sum_{j=1..11} a(n-j) - 45*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 10*x + 54*x^12 - 45*x^13). (End)` (gf-factored)
* `%F a(n) = 9*Sum_{j=1..11} a(n-j) - 45*a(n-12).` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^12)/(1-10*t+54*t^12-45*t^13), {t, 0, 50}], t] (* _G. C. Greubel_, May 17 2016; Aug 23 2024 *)` (wolfram-series)
* `%T coxG[{12,45,-9}]` (wolfram-coxG)
* `%O R<x>:=PowerSeriesRing(Integers(), 30); Coefficients(R!( (1+x)*(1-x^12)/(1-10*x+54*x^12-45*x^13) )); // _G. C. Greubel_, Aug 23 2024` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166551

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166551 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A166551 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166551
