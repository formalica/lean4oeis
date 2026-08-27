import LOEIS.A167.A167693.Defs

/-!
# A167693 — program transcriptions (`Equiv_706fd1e320cd309c`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(210*t^15 - 20*t^14 - 20*t^13 - 20*t^12 - 20*t^11 - 20*t^10 - 20*t^9 - 20*t^8 - 20*t^7 - 20*t^6 - 20*t^5 - 20*t^4 - 20*t^3 - 20*t^2 - 20*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(210*t^15 - 20*t^14 - 20*t^13 - 20*t^12 - 20*t^11 - 20*t^10 - 20*t^9 - 20*t^8 - 20*t^7 - 20*t^6 - 20*t^5 - 20*t^4 - 20*t^3 - 20*t^2 - 20*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Jun 20 2016 *)` (wolfram-series)
* `%O (PARI) first(n)=Vec((1+x^5+x^10)*(1+x+x^2+x^3+x^4)*(1+x)/(1-20*x-20*x^2-20*x^3-20*x^4-20*x^5-20*x^6-20*x^7-20*x^8-20*x^9-20*x^10-20*x^11-20*x^12-20*x^13-20*x^14+210*x^15)+O(x^(n+1))) \\ _Charles R Greathouse IV_, Jun 12 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167693

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167693 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167693 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167693
