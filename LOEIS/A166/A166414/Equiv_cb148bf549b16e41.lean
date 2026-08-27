import LOEIS.A166.A166414.Defs

/-!
# A166414 — program transcriptions (`Equiv_cb148bf549b16e41`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(171*t^11 - 18*t^10 - 18*t^9 - 18*t^8 - 18*t^7 - 18*t^6 - 18*t^5 - 18*t^4 - 18*t^3 - 18*t^2 - 18*t + 1). From _G. C. Greubel_, Jul 23 2024: (Start) a(n) = 18*Sum_{j=1..10} a(n-j) - 171*a(n-11). G.f.: (1+x)*(1 - x^11)/(1 - 19*x + 189*x^11 - 171*x^12). (End)` (gf-rational)
* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(171*t^11 - 18*t^10 - 18*t^9 - 18*t^8 - 18*t^7 - 18*t^6 - 18*t^5 - 18*t^4 - 18*t^3 - 18*t^2 - 18*t + 1). From _G. C. Greubel_, Jul 23 2024: (Start) a(n) = 18*Sum_{j=1..10} a(n-j) - 171*a(n-11). G.f.: (1+x)*(1 - x^11)/(1 - 19*x + 189*x^11 - 171*x^12). (End)` (gf-factored)
* `%F a(n) = 18*Sum_{j=1..10} a(n-j) - 171*a(n-11).` (recurrence)
* `%T coxG[{11,171,-18}]` (wolfram-coxG)
* `%T CoefficientList[Series[(1+t)*(1-t^11)/(1-19*t+189*t^11-171*t^12), {t, 0,50}], t] (* _G. C. Greubel_, May 12 2016; Jul 23 2024 *)` (wolfram-series)
* `%O (PARI) Vec((1+x+x^2+x^3+x^4+x^5+x^6+x^7+x^8+x^9+x^10)*(1+x)/(1-18*x-18*x^2-18*x^3-18*x^4-18*x^5-18*x^6-18*x^7-18*x^8-18*x^9-18*x^10+171*x^11)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166414

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166414 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A166414 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166414
