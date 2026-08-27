import LOEIS.A166.A166435.Defs

/-!
# A166435 — program transcriptions (`Equiv_759b6145765d406e`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(780*t^11 - 39*t^10 - 39*t^9 - 39*t^8 - 39*t^7 - 39*t^6 - 39*t^5 - 39*t^4 - 39*t^3 - 39*t^2 - 39*t + 1). From _G. C. Greubel_, Jul 26 2024: (Start) a(n) = 39*Sum_{j=1..10} a(n-j) - 780*a(n-11). G.f.: (1+x)*(1-x^11)/(1 - 40*x + 819*x^11 - 780*x^12). (End)` (gf-rational)
* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(780*t^11 - 39*t^10 - 39*t^9 - 39*t^8 - 39*t^7 - 39*t^6 - 39*t^5 - 39*t^4 - 39*t^3 - 39*t^2 - 39*t + 1). From _G. C. Greubel_, Jul 26 2024: (Start) a(n) = 39*Sum_{j=1..10} a(n-j) - 780*a(n-11). G.f.: (1+x)*(1-x^11)/(1 - 40*x + 819*x^11 - 780*x^12). (End)` (gf-factored)
* `%F a(n) = 39*Sum_{j=1..10} a(n-j) - 780*a(n-11).` (recurrence)
* `%T With[{p=780, q=39}, CoefficientList[Series[(1+t)*(1-t^11)/(1 - (q+1)*t + (p+q)*t^11 - p*t^12), {t,0,40}], t]] (* _G. C. Greubel_, May 14 2016; Jul 26 2024 *)` (wolfram-series)
* `%T coxG[{11, 780, -39, 30}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x+x^2+x^3+x^4+x^5+x^6+x^7+x^8+x^9+x^10)*(1+x)/(1-39*x-39*x^2-39*x^3-39*x^4-39*x^5-39*x^6-39*x^7-39*x^8-39*x^9-39*x^10+780*x^11)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166435

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166435 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166435 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166435
