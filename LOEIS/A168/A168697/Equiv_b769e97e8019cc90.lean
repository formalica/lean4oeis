import LOEIS.A168.A168697.Defs

/-!
# A168697 — program transcriptions (`Equiv_b769e97e8019cc90`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/ (171*t^17 - 18*t^16 - 18*t^15 - 18*t^14 - 18*t^13 - 18*t^12 - 18*t^11 - 18*t^10 - 18*t^9 - 18*t^8 - 18*t^7 - 18*t^6 - 18*t^5 - 18*t^4 - 18*t^3 - 18*t^2 - 18*t + 1).` (gf-rational)
* `%T coxG[{17,171,-18}]` (wolfram-coxG)
* `%T CoefficientList[Series[(t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(171*t^17 - 18*t^16 - 18*t^15 - 18*t^14 - 18*t^13 - 18*t^12 - 18*t^11 - 18*t^10 - 18*t^9 - 18*t^8 - 18*t^7 - 18*t^6 - 18*t^5 - 18*t^4 - 18*t^3 - 18*t^2 - 18*t + 1), {t,0,50}], t] (* _G. C. Greubel_, Aug 03 2016 *)` (wolfram-series)
* `%O (PARI) first(n)=Vec((1+x+x^2+x^3+x^4+x^5+x^6+x^7+x^8+x^9+x^10+x^11+x^12+x^13+x^14+x^15+x^16)*(1+x)/(1-18*x-18*x^2-18*x^3-18*x^4-18*x^5-18*x^6-18*x^7-18*x^8-18*x^9-18*x^10-18*x^11-18*x^12-18*x^13-18*x^14-18*x^15-18*x^16+171*x^17)+O(x^(n+1))) \\ _Charles R Greathouse IV_, Jul 05 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168697

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168697 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A168697 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168697
