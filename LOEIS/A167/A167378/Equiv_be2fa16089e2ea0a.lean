import LOEIS.A167.A167378.Defs

/-!
# A167378 — program transcriptions (`Equiv_be2fa16089e2ea0a`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(435*t^14 - 29*t^13 - 29*t^12 - 29*t^11 - 29*t^10 - 29*t^9 - 29*t^8 - 29*t^7 - 29*t^6 - 29*t^5 - 29*t^4 - 29*t^3 - 29*t^2 - 29*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/ (435*t^14 - 29*t^13 - 29*t^12 - 29*t^11 - 29*t^10 - 29*t^9 - 29*t^8 - 29*t^7 - 29*t^6 - 29*t^5 - 29*t^4 - 29*t^3 - 29*t^2 - 29*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Jun 12 2016 *)` (wolfram-series)
* `%T coxG[{14,435,-29}]` (wolfram-coxG)
* `%O (PARI) first(n)=Vec((1+x^2+x^4+x^6+x^8+x^10+x^12)*(1+x)^2/(1-29*x-29*x^2-29*x^3-29*x^4-29*x^5-29*x^6-29*x^7-29*x^8-29*x^9-29*x^10-29*x^11-29*x^12-29*x^13+435*x^14)+O(x^(n+1))) \\ _Charles R Greathouse IV_, Jun 11 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167378

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167378 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167378 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167378
