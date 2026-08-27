import LOEIS.A166.A166543.Defs

/-!
# A166543 — program transcriptions (`Equiv_6c544649897e5457`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(36*t^12 - 8*t^11 - 8*t^10 - 8*t^9 - 8*t^8 - 8*t^7 - 8*t^6 - 8*t^5 - 8*t^4 - 8*t^3 - 8*t^2 - 8*t + 1). From _G. C. Greubel_, Aug 23 2024: (Start) a(n) = 8*Sum_{j=1..11} a(n-j) - 36*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 9*x + 44*x^12 - 36*x^13). (End)` (gf-rational)
* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(36*t^12 - 8*t^11 - 8*t^10 - 8*t^9 - 8*t^8 - 8*t^7 - 8*t^6 - 8*t^5 - 8*t^4 - 8*t^3 - 8*t^2 - 8*t + 1). From _G. C. Greubel_, Aug 23 2024: (Start) a(n) = 8*Sum_{j=1..11} a(n-j) - 36*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 9*x + 44*x^12 - 36*x^13). (End)` (gf-factored)
* `%F a(n) = 8*Sum_{j=1..11} a(n-j) - 36*a(n-12).` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^12)/(1-9*t+44*t^12-36*t^13), {t, 0, 50}], t] (* _G. C. Greubel_, May 16 2016; Aug 23 2024 *)` (wolfram-series)
* `%T coxG[{12,36,-8,30}]` (wolfram-coxG)
* `%O R<x>:=PowerSeriesRing(Integers(), 30); Coefficients(R!( (1+x)*(1-x^12)/(1-9*x+44*x^12-36*x^13) )); // _G. C. Greubel_, Aug 23 2024` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166543

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166543 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A166543 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166543
