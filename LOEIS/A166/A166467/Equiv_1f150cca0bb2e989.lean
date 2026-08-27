import LOEIS.A166.A166467.Defs

/-!
# A166467 — program transcriptions (`Equiv_1f150cca0bb2e989`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(t^12 - t^11 - t^10 - t^9 - t^8 - t^7 - t^6 - t^5 - t^4 - t^3 - t^2 - t + 1). From _G. C. Greubel_, Jul 28 2024: (Start) a(n) = Sum_{j=1..11} a(n-j) - a(n-11). G.f.: (1+x)*(1-x^12)/(1 - 2*x + 2*x^12 - x^13). (End)` (gf-rational)
* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(t^12 - t^11 - t^10 - t^9 - t^8 - t^7 - t^6 - t^5 - t^4 - t^3 - t^2 - t + 1). From _G. C. Greubel_, Jul 28 2024: (Start) a(n) = Sum_{j=1..11} a(n-j) - a(n-11). G.f.: (1+x)*(1-x^12)/(1 - 2*x + 2*x^12 - x^13). (End)` (gf-factored)
* `%F a(n) = Sum_{j=1..11} a(n-j) - a(n-11).` (recurrence)
* `%T With[{p=1, q=1}, CoefficientList[Series[(1+t)*(1-t^12)/(1-(q+1)*t + (p+ q)*t^12-p*t^13), {t,0,40}], t]] (* _G. C. Greubel_, May 15 2016; Jul 28 2024 *)` (wolfram-series)
* `%T coxG[{12,1,-1,40}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x^4+x^8)*(1+x^2)*(1+x)^2/(1-x-x^2-x^3-x^4-x^5-x^6-x^7-x^8-x^9-x^10-x^11+x^12)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166467

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166467 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166467 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166467
