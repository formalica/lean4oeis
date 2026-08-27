import LOEIS.A167.A167235.Defs

/-!
# A167235 — program transcriptions (`Equiv_340e5f141ede4ba4`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(351*t^14 - 26*t^13 - 26*t^12 - 26*t^11 - 26*t^10 - 26*t^9 - 26*t^8 - 26*t^7 - 26*t^6 - 26*t^5 - 26*t^4 - 26*t^3 - 26*t^2 - 26*t + 1).` (gf-rational)
* `%T coxG[{14,351,-26}]` (wolfram-coxG)
* `%T CoefficientList[Series[(t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/ (351*t^14 - 26*t^13 - 26*t^12 - 26*t^11 - 26*t^10 - 26*t^9 - 26*t^8 - 26*t^7 - 26*t^6 - 26*t^5 - 26*t^4 - 26*t^3 - 26*t^2 - 26*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Jun 05 2016 *)` (wolfram-series)
* `%O (PARI) first(n)=Vec((1+x^2+x^4+x^6+x^8+x^10+x^12)*(1+x)^2/(1-26*x-26*x^2-26*x^3-26*x^4-26*x^5-26*x^6-26*x^7-26*x^8-26*x^9-26*x^10-26*x^11-26*x^12-26*x^13+351*x^14)+O(x^(n+1))) \\ _Charles R Greathouse IV_, Jun 11 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167235

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167235 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167235 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167235
