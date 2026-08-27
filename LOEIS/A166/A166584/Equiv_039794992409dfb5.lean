import LOEIS.A166.A166584.Defs

/-!
# A166584 — program transcriptions (`Equiv_039794992409dfb5`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(105*t^12 - 14*t^11 - 14*t^10 - 14*t^9 -14*t^8 - 14*t^7 - 14*t^6 - 14*t^5 - 14*t^4 - 14*t^3 - 14*t^2 -14*t +1). From _G. C. Greubel_, Dec 04 2024: (Start) a(n) = 14*Sum_{j=1..11} a(n-j) - 105*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 15*x + 119*x^12 - 105*x^13). (End)` (gf-rational)
* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(105*t^12 - 14*t^11 - 14*t^10 - 14*t^9 -14*t^8 - 14*t^7 - 14*t^6 - 14*t^5 - 14*t^4 - 14*t^3 - 14*t^2 -14*t +1). From _G. C. Greubel_, Dec 04 2024: (Start) a(n) = 14*Sum_{j=1..11} a(n-j) - 105*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 15*x + 119*x^12 - 105*x^13). (End)` (gf-factored)
* `%F a(n) = 14*Sum_{j=1..11} a(n-j) - 105*a(n-12).` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^12)/(1-15*t+119*t^12-105*t^13), {t,0,50}], t] (* _G. C. Greubel_, May 17 2016; Dec 04 2024 *)` (wolfram-series)
* `%T coxG[{12,105,-14}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x^4+x^8)*(1+x^2)*(1+x)^2/(1-14*x-14*x^2-14*x^3-14*x^4-14*x^5-14*x^6-14*x^7-14*x^8-14*x^9-14*x^10-14*x^11+105*x^12)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166584

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166584 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166584 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166584
