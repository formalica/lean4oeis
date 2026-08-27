import LOEIS.A167.A167110.Defs

/-!
# A167110 — program transcriptions (`Equiv_10a80307be055939`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(28*t^14 - 7*t^13 - 7*t^12 - 7*t^11 - 7*t^10 - 7*t^9 - 7*t^8 - 7*t^7 - 7*t^6 - 7*t^5 - 7*t^4 - 7*t^3 - 7*t^2 - 7*t + 1).` (gf-rational)
* `%T coxG[{14,28,-7}]` (wolfram-coxG)
* `%T CoefficientList[Series[(t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/ (28*t^14 - 7*t^13 - 7*t^12 - 7*t^11 - 7*t^10 - 7*t^9 - 7*t^8 - 7*t^7 - 7*t^6 - 7*t^5 - 7*t^4 - 7*t^3 - 7*t^2 - 7*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Jun 03 2016 *)` (wolfram-series)
* `%O (PARI) first(n)=Vec((1+x^2+x^4+x^6+x^8+x^10+x^12)*(1+x)^2/(1-7*x-7*x^2-7*x^3-7*x^4-7*x^5-7*x^6-7*x^7-7*x^8-7*x^9-7*x^10-7*x^11-7*x^12-7*x^13+28*x^14)+O(x^(n+1))) \\ _Charles R Greathouse IV_, Jun 11 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167110

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167110 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167110 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167110
