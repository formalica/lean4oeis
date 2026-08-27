import LOEIS.A167.A167757.Defs

/-!
# A167757 — program transcriptions (`Equiv_49bbb80b497e37b3`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(465*t^15 - 30*t^14 - 30*t^13 - 30*t^12 - 30*t^11 - 30*t^10 - 30*t^9 - 30*t^8 - 30*t^7 - 30*t^6 - 30*t^5 - 30*t^4 - 30*t^3 - 30*t^2 - 30*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(465*t^15 - 30*t^14 - 30*t^13 - 30*t^12 - 30*t^11 - 30*t^10 - 30*t^9 - 30*t^8 - 30*t^7 - 30*t^6 - 30*t^5 - 30*t^4 - 30*t^3 - 30*t^2 - 30*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Jun 23 2016 *)` (wolfram-series)
* `%O (PARI) first(n)=Vec((1+x^5+x^10)*(1+x+x^2+x^3+x^4)*(1+x)/(1-30*x-30*x^2-30*x^3-30*x^4-30*x^5-30*x^6-30*x^7-30*x^8-30*x^9-30*x^10-30*x^11-30*x^12-30*x^13-30*x^14+465*x^15)+O(x^(n+1))) \\ _Charles R Greathouse IV_, Jun 13 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167757

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167757 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167757 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167757
