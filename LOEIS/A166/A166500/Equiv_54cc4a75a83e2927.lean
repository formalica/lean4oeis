import LOEIS.A166.A166500.Defs

/-!
# A166500 — program transcriptions (`Equiv_54cc4a75a83e2927`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(10*t^12 - 4*t^11 - 4*t^10 - 4*t^9 - 4*t^8 - 4*t^7 - 4*t^6 - 4*t^5 - 4*t^4 - 4*t^3 - 4*t^2 - 4*t + 1). From _G. C. Greubel_, Aug 03 2024: (Start) a(n) = 4*Sum_{j=1..11} a(n-j) - 10*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 5*x + 14*x^12 - 10*x^13). (End)` (gf-rational)
* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(10*t^12 - 4*t^11 - 4*t^10 - 4*t^9 - 4*t^8 - 4*t^7 - 4*t^6 - 4*t^5 - 4*t^4 - 4*t^3 - 4*t^2 - 4*t + 1). From _G. C. Greubel_, Aug 03 2024: (Start) a(n) = 4*Sum_{j=1..11} a(n-j) - 10*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 5*x + 14*x^12 - 10*x^13). (End)` (gf-factored)
* `%F a(n) = 4*Sum_{j=1..11} a(n-j) - 10*a(n-12).` (recurrence)
* `%T With[{p=10, q=4}, CoefficientList[Series[(1+t)*(1-t^12)/(1 - (q+1)*t + (p+q)*t^12 - p*t^13), {t,0,40}], t]] (* _G. C. Greubel_, May 15 2016; Aug 02 2024 *)` (wolfram-series)
* `%T coxG[{12, 10, -4, 30}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166500

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166500 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166500 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166500
