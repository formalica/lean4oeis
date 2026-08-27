import LOEIS.A167.A167212.Defs

/-!
# A167212 — program transcriptions (`Equiv_172111921cf4fbf0`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(276*t^14 - 23*t^13 - 23*t^12 - 23*t^11 - 23*t^10 - 23*t^9 - 23*t^8 - 23*t^7 - 23*t^6 - 23*t^5 - 23*t^4 - 23*t^3 - 23*t^2 - 23*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/ (276*t^14 - 23*t^13 - 23*t^12 - 23*t^11 - 23*t^10 - 23*t^9 - 23*t^8 - 23*t^7 - 23*t^6 - 23*t^5 - 23*t^4 - 23*t^3 - 23*t^2 - 23*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Jun 05 2016 *)` (wolfram-series)
* `%O (PARI) first(n)=Vec((1+x^2+x^4+x^6+x^8+x^10+x^12)*(1+x)^2/(1-23*x-23*x^2-23*x^3-23*x^4-23*x^5-23*x^6-23*x^7-23*x^8-23*x^9-23*x^10-23*x^11-23*x^12-23*x^13+276*x^14)+O(x^(n+1))) \\ _Charles R Greathouse IV_, Jun 11 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167212

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167212 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167212 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167212
