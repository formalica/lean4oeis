import LOEIS.A167.A167861.Defs

/-!
# A167861 — program transcriptions (`Equiv_13ae2983b523a6d4`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(990*t^15 - 44*t^14 - 44*t^13 - 44*t^12 - 44*t^11 - 44*t^10 - 44*t^9 - 44*t^8 - 44*t^7 - 44*t^6 - 44*t^5 - 44*t^4 - 44*t^3 - 44*t^2 - 44*t + 1).` (gf-rational)
* `%T coxG[{15,990,-44}]` (wolfram-coxG)
* `%T CoefficientList[Series[(t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(990*t^15 - 44*t^14 - 44*t^13 - 44*t^12 - 44*t^11 - 44*t^10 - 44*t^9 - 44*t^8 - 44*t^7 - 44*t^6 - 44*t^5 - 44*t^4 - 44*t^3 - 44*t^2 - 44*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Jun 28 2016 *)` (wolfram-series)
* `%O (PARI) first(n)=Vec((1+x^5+x^10)*(1+x+x^2+x^3+x^4)*(1+x)/(1-44*x-44*x^2-44*x^3-44*x^4-44*x^5-44*x^6-44*x^7-44*x^8-44*x^9-44*x^10-44*x^11-44*x^12-44*x^13-44*x^14+990*x^15)+O(x^(n+1))) \\ _Charles R Greathouse IV_, Aug 14 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167861

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167861 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167861 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167861
