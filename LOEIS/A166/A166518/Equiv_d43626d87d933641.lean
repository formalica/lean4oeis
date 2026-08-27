import LOEIS.A166.A166518.Defs

/-!
# A166518 — program transcriptions (`Equiv_d43626d87d933641`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(15*t^12 - 5*t^11 - 5*t^10 - 5*t^9 - 5*t^8 - 5*t^7 - 5*t^6 - 5*t^5 - 5*t^4 - 5*t^3 - 5*t^2 - 5*t + 1). From _G. C. Greubel_, Aug 03 2024: (Start) a(n) = 5*Sum_{j=1..11} a(n-j) - 15*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 6*x + 20*x^12 - 15*x^13). (End)` (gf-rational)
* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(15*t^12 - 5*t^11 - 5*t^10 - 5*t^9 - 5*t^8 - 5*t^7 - 5*t^6 - 5*t^5 - 5*t^4 - 5*t^3 - 5*t^2 - 5*t + 1). From _G. C. Greubel_, Aug 03 2024: (Start) a(n) = 5*Sum_{j=1..11} a(n-j) - 15*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 6*x + 20*x^12 - 15*x^13). (End)` (gf-factored)
* `%F a(n) = 5*Sum_{j=1..11} a(n-j) - 15*a(n-12).` (recurrence)
* `%T With[{p=15, q=5}, CoefficientList[Series[(1+t)*(1-t^12)/(1 - (q+1)*t + (p+q)*t^12 - p*t^13), {t,0,40}], t]] (* _G. C. Greubel_, May 15 2016; Aug 03 2024 *)` (wolfram-series)
* `%T coxG[{12, 15, -5, 30}]` (wolfram-coxG)
* `%O (PARI) Vec((t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(15*t^12 - 5*t^11 - 5*t^10 - 5*t^9 - 5*t^8 - 5*t^7 - 5*t^6 - 5*t^5 - 5*t^4 - 5*t^3 - 5*t^2 - 5*t + 1)+O(t^99))` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166518

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166518 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166518 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166518
