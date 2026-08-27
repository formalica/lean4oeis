import LOEIS.A166.A166603.Defs

/-!
# A166603 — program transcriptions (`Equiv_653e81c2cacb00da`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(190*t^12 - 19*t^11 - 19*t^10 - 19*t^9 -19*t^8 -19*t^7 - 19*t^6 - 19*t^5 - 19*t^4 - 19*t^3 - 19*t^2 - 19*t +1). From _G. C. Greubel_, Jan 21 2025: (Start) a(n) = 19*Sum_{j=1..11} a(n-j) - 190*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 20*x + 209*x^12 - 190*x^13). (End)` (gf-rational)
* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(190*t^12 - 19*t^11 - 19*t^10 - 19*t^9 -19*t^8 -19*t^7 - 19*t^6 - 19*t^5 - 19*t^4 - 19*t^3 - 19*t^2 - 19*t +1). From _G. C. Greubel_, Jan 21 2025: (Start) a(n) = 19*Sum_{j=1..11} a(n-j) - 190*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 20*x + 209*x^12 - 190*x^13). (End)` (gf-factored)
* `%F a(n) = 19*Sum_{j=1..11} a(n-j) - 190*a(n-12).` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^12)/(1-20*t+209*t^12-190*t^13), {t,0,50}], t] (* _G. C. Greubel_, May 18 2016; Jan 21 2025 *)` (wolfram-series)
* `%T coxG[{12,190,-19}]` (wolfram-coxG)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 50); Coefficients(R!( (1+x)*(1-x^12)/(1-20*x+209*x^12-190*x^13) )); // _G. C. Greubel_, Jan 21 2025` (magma-series)
* `%O (PARI) Vec((1+x^4+x^8)*(1+x^2)*(1+x)^2/(1-19*x-19*x^2-19*x^3-19*x^4-19*x^5-19*x^6-19*x^7-19*x^8-19*x^9-19*x^10-19*x^11+190*x^12)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166603

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166603 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166603 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166603
