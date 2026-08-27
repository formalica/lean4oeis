import LOEIS.A166.A166495.Defs

/-!
# A166495 — program transcriptions (`Equiv_101229dc38d9f20a`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(6*t^12 - 3*t^11 - 3*t^10 - 3*t^9 - 3*t^8 - 3*t^7 - 3*t^6 - 3*t^5 - 3*t^4 - 3*t^3 - 3*t^2 - 3*t + 1). From _G. C. Greubel_, Aug 02 2024: (Start) a(n) = 3*Sum_{j=1..11} a(n-j) - 6*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 4*x + 9*x^12 - 6*x^13). (End)` (gf-rational)
* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(6*t^12 - 3*t^11 - 3*t^10 - 3*t^9 - 3*t^8 - 3*t^7 - 3*t^6 - 3*t^5 - 3*t^4 - 3*t^3 - 3*t^2 - 3*t + 1). From _G. C. Greubel_, Aug 02 2024: (Start) a(n) = 3*Sum_{j=1..11} a(n-j) - 6*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 4*x + 9*x^12 - 6*x^13). (End)` (gf-factored)
* `%F a(n) = 3*Sum_{j=1..11} a(n-j) - 6*a(n-12).` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^12)/(1-4*t+9*t^12-6*t^13), {t, 0, 50}], t] (* _G. C. Greubel_, May 15 2016; Aug 02 2024 *)` (wolfram-series)
* `%T coxG[{12,6,-3,30}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x^4+x^8)*(1+x^2)*(1+x)^2/(1-3*x-3*x^2-3*x^3-3*x^4-3*x^5-3*x^6-3*x^7-3*x^8-3*x^9-3*x^10-3*x^11+6*x^12)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166495

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166495 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A166495 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166495
