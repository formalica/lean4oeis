import LOEIS.A166.A166568.Defs

/-!
# A166568 — program transcriptions (`Equiv_68f5eac6231edfdd`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(78*t^12 - 12*t^11 - 12*t^10 - 12*t^9 - 12*t^8 - 12*t^7 - 12*t^6 - 12*t^5 - 12*t^4 - 12*t^3 - 12*t^2 - 12*t +1). From _G. C. Greubel_, Dec 03 2024: (Start) a(n) = 12*Sum_{j=1..11} a(n-j) - 78*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 13*x + 90*x^12 - 78*x^13). (End)` (gf-rational)
* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(78*t^12 - 12*t^11 - 12*t^10 - 12*t^9 - 12*t^8 - 12*t^7 - 12*t^6 - 12*t^5 - 12*t^4 - 12*t^3 - 12*t^2 - 12*t +1). From _G. C. Greubel_, Dec 03 2024: (Start) a(n) = 12*Sum_{j=1..11} a(n-j) - 78*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 13*x + 90*x^12 - 78*x^13). (End)` (gf-factored)
* `%F a(n) = 12*Sum_{j=1..11} a(n-j) - 78*a(n-12).` (recurrence)
* `%T coxG[{12,78,-12}]` (wolfram-coxG)
* `%T CoefficientList[Series[(1+t)*(1-t^12)/(1-13*t+90*t^12-78*t^13), {t,0,50}], t] (* _G. C. Greubel_, May 17 2016; Dec 03 2024 *)` (wolfram-series)
* `%O (PARI) Vec((1+x^4+x^8)*(1+x^2)*(1+x)^2/(1-12*x-12*x^2-12*x^3-12*x^4-12*x^5-12*x^6-12*x^7-12*x^8-12*x^9-12*x^10-12*x^11+78*x^12)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166568

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166568 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166568 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166568
