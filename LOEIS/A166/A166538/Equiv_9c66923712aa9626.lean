import LOEIS.A166.A166538.Defs

/-!
# A166538 — program transcriptions (`Equiv_9c66923712aa9626`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(21*t^12 - 6*t^11 - 6*t^10 - 6*t^9 - 6*t^8 - 6*t^7 - 6*t^6 - 6*t^5 - 6*t^4 - 6*t^3 - 6*t^2 - 6*t + 1). From _G. C. Greubel_, Aug 23 2024: (Start) a(n) = 6*Sum_{j=1..11} a(n-j) - 21*a(n-12). G.f.: (1 + x)*(1 - x^12)/(1 - 7*x + 27*x^12 - 21*x^13). (End)` (gf-rational)
* `%F a(n) = 6*Sum_{j=1..11} a(n-j) - 21*a(n-12).` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^12)/(1-7*t+27*t^12-21*t^13), {t, 0, 50}], t] (* _G. C. Greubel_, May 16 2016; Aug 23 2024 *)` (wolfram-series)
* `%T coxG[{12,21,-6}]` (wolfram-coxG)
* `%O R<x>:=PowerSeriesRing(Integers(), 30); Coefficients(R!( (1+x)*(1-x^12)/(1-7*x+27*x^12-21*x^13) )); // _G. C. Greubel_, Aug 23 2024` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166538

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166538 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A166538 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166538
