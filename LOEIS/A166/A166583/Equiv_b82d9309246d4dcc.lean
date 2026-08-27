import LOEIS.A166.A166583.Defs

/-!
# A166583 — program transcriptions (`Equiv_b82d9309246d4dcc`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(91*t^12 - 13*t^11 - 13*t^10 - 13*t^9 - 13*t^8 - 13*t^7 - 13*t^6 - 13*t^5 - 13*t^4 - 13*t^3 - 13*t^2 - 13*t +1). From _G. C. Greubel_, Dec 03 2024: (Start) a(n) = 13*Sum_{j=1..11} a(n-j) - 91*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 14*x + 104*x^12 - 91*x^13). (End)` (gf-rational)
* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(91*t^12 - 13*t^11 - 13*t^10 - 13*t^9 - 13*t^8 - 13*t^7 - 13*t^6 - 13*t^5 - 13*t^4 - 13*t^3 - 13*t^2 - 13*t +1). From _G. C. Greubel_, Dec 03 2024: (Start) a(n) = 13*Sum_{j=1..11} a(n-j) - 91*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 14*x + 104*x^12 - 91*x^13). (End)` (gf-factored)
* `%F a(n) = 13*Sum_{j=1..11} a(n-j) - 91*a(n-12).` (recurrence)
* `%T CoefficientList[Series[(1+x)*(1-x^12)/(1 - 14*x + 104*x^12 - 91*x^13), {t, 0, 50}], t] (* _G. C. Greubel_, May 17 2016; Dec 03 2024 *)` (wolfram-series)
* `%T coxG[{12,91,-13}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x^4+x^8)*(1+x^2)*(1+x)^2/(1-13*x-13*x^2-13*x^3-13*x^4-13*x^5-13*x^6-13*x^7-13*x^8-13*x^9-13*x^10-13*x^11+91*x^12)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166583

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166583 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A166583 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166583
