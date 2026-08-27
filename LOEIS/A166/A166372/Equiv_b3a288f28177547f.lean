import LOEIS.A166.A166372.Defs

/-!
# A166372 — program transcriptions (`Equiv_b3a288f28177547f`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(55*t^11 - 10*t^10 - 10*t^9 - 10*t^8 - 10*t^7 - 10*t^6 - 10*t^5 - 10*t^4 - 10*t^3 - 10*t^2 - 10*t + 1). From _G. C. Greubel_, Dec 06 2024: (Start) a(n) = 10*Sum_{j=1..10} a(n-j) - 55*a(n-11). G.f.: (1+x)*(1-x^11)/(1 - 11*x + 65*x^11 - 55*x^12). (End)` (gf-rational)
* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(55*t^11 - 10*t^10 - 10*t^9 - 10*t^8 - 10*t^7 - 10*t^6 - 10*t^5 - 10*t^4 - 10*t^3 - 10*t^2 - 10*t + 1). From _G. C. Greubel_, Dec 06 2024: (Start) a(n) = 10*Sum_{j=1..10} a(n-j) - 55*a(n-11). G.f.: (1+x)*(1-x^11)/(1 - 11*x + 65*x^11 - 55*x^12). (End)` (gf-factored)
* `%F a(n) = 10*Sum_{j=1..10} a(n-j) - 55*a(n-11).` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^11)/(1-11*t+65*t^11-55*t^12), {t,0,50}], t] (* _G. C. Greubel_, May 10 2016; Dec 06 2024 *)` (wolfram-series)
* `%T coxG[{11,55,-10,40}]` (wolfram-coxG)
* `%O R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1-x^11)/(1-11*x+65*x^11-55*x^12) )); // _G. C. Greubel_, Dec 06 2024` (magma-series)
* `%O (PARI) Vec((1+x+x^2+x^3+x^4+x^5+x^6+x^7+x^8+x^9+x^10)*(1+x)/(1-10*x-10*x^2-10*x^3-10*x^4-10*x^5-10*x^6-10*x^7-10*x^8-10*x^9-10*x^10+55*x^11)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166372

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166372 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166372 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166372
