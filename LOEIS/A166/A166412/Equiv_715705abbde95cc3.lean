import LOEIS.A166.A166412.Defs

/-!
# A166412 — program transcriptions (`Equiv_715705abbde95cc3`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(136*t^11 - 16*t^10 - 16*t^9 - 16*t^8 - 16*t^7 - 16*t^6 - 16*t^5 - 16*t^4 - 16*t^3 - 16*t^2 - 16*t + 1). From _G. C. Greubel_, Jul 23 2024: (Start) a(n) = 16*Sum_{j=1..10} a(n-j) - 136*a(n-11). G.f.: (1+x)*(1 - x^11)/(1 - 17*x + 152*x^11 - 136*x^12). (End)` (gf-rational)
* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(136*t^11 - 16*t^10 - 16*t^9 - 16*t^8 - 16*t^7 - 16*t^6 - 16*t^5 - 16*t^4 - 16*t^3 - 16*t^2 - 16*t + 1). From _G. C. Greubel_, Jul 23 2024: (Start) a(n) = 16*Sum_{j=1..10} a(n-j) - 136*a(n-11). G.f.: (1+x)*(1 - x^11)/(1 - 17*x + 152*x^11 - 136*x^12). (End)` (gf-factored)
* `%F a(n) = 16*Sum_{j=1..10} a(n-j) - 136*a(n-11).` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^11)/(1-17*t+152*t^11-136*t^12), {t, 0,50}], t] (* _G. C. Greubel_, May 12 2016; Jul 23 2024 *)` (wolfram-series)
* `%T coxG[{11, 136, -16, 30}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x+x^2+x^3+x^4+x^5+x^6+x^7+x^8+x^9+x^10)*(1+x)/(1-16*x-16*x^2-16*x^3-16*x^4-16*x^5-16*x^6-16*x^7-16*x^8-16*x^9-16*x^10+136*x^11)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166412

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166412 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A166412 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166412
