import LOEIS.A168.A168698.Defs

/-!
# A168698 — program transcriptions (`Equiv_a4cc5b9d87d68910`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(190*t^17 - 19*t^16 - 19*t^15 - 19*t^14 - 19*t^13 - 19*t^12 - 19*t^11 - 19*t^10 - 19*t^9 - 19*t^8 - 19*t^7 - 19*t^6 - 19*t^5 - 19*t^4 - 19*t^3 - 19*t^2 - 19*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(190*t^17 - 19*t^16 - 19*t^15 - 19*t^14 - 19*t^13 - 19*t^12 - 19*t^11 - 19*t^10 - 19*t^9 - 19*t^8 - 19*t^7 - 19*t^6 - 19*t^5 - 19*t^4 - 19*t^3 - 19*t^2 - 19*t + 1), {t,0,50}], t] (* _G. C. Greubel_, Aug 04 2016 *)` (wolfram-series)
* `%O (PARI) first(n)=Vec((1+x+x^2+x^3+x^4+x^5+x^6+x^7+x^8+x^9+x^10+x^11+x^12+x^13+x^14+x^15+x^16)*(1+x)/(1-19*x-19*x^2-19*x^3-19*x^4-19*x^5-19*x^6-19*x^7-19*x^8-19*x^9-19*x^10-19*x^11-19*x^12-19*x^13-19*x^14-19*x^15-19*x^16+190*x^17)+O(x^(n+1))) \\ _Charles R Greathouse IV_, Jul 05 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168698

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168698 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A168698 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168698
