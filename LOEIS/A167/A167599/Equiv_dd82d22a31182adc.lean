import LOEIS.A167.A167599.Defs

/-!
# A167599 — program transcriptions (`Equiv_dd82d22a31182adc`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(820*t^14 - 40*t^13 - 40*t^12 - 40*t^11 - 40*t^10 - 40*t^9 - 40*t^8 - 40*t^7 - 40*t^6 - 40*t^5 - 40*t^4 - 40*t^3 - 40*t^2 - 40*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/ (820*t^14 - 40*t^13 - 40*t^12 - 40*t^11 - 40*t^10 - 40*t^9 - 40*t^8 - 40*t^7 - 40*t^6 - 40*t^5 - 40*t^4 - 40*t^3 - 40*t^2 - 40*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Jun 17 2016 *)` (wolfram-series)
* `%O (PARI) first(n)=Vec((1+x^2+x^4+x^6+x^8+x^10+x^12)*(1+x)^2/(1-40*x-40*x^2-40*x^3-40*x^4-40*x^5-40*x^6-40*x^7-40*x^8-40*x^9-40*x^10-40*x^11-40*x^12-40*x^13+820*x^14)+O(x^(n+1))) \\ _Charles R Greathouse IV_, Jun 11 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167599

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167599 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167599 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167599
