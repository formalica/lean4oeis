import LOEIS.A167.A167653.Defs

/-!
# A167653 — program transcriptions (`Equiv_7b38b4ede9467568`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(21*t^15 - 6*t^14 - 6*t^13 - 6*t^12 - 6*t^11 - 6*t^10 - 6*t^9 - 6*t^8 - 6*t^7 - 6*t^6 - 6*t^5 - 6*t^4 - 6*t^3 - 6*t^2 - 6*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(21*t^15 - 6*t^14 - 6*t^13 - 6*t^12 - 6*t^11 - 6*t^10 - 6*t^9 - 6*t^8 - 6*t^7 - 6*t^6 - 6*t^5 - 6*t^4 - 6*t^3 - 6*t^2 - 6*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Jun 18 2016 *)` (wolfram-series)
* `%O (PARI) first(n)=Vec((1+x^5+x^10)*(1+x+x^2+x^3+x^4)*(1+x)/(1-6*x-6*x^2-6*x^3-6*x^4-6*x^5-6*x^6-6*x^7-6*x^8-6*x^9-6*x^10-6*x^11-6*x^12-6*x^13-6*x^14+21*x^15)+O(x^(n+1))) \\ _Charles R Greathouse IV_, Jun 12 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167653

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167653 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167653 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167653
