import LOEIS.A167.A167027.Defs

/-!
# A167027 — program transcriptions (`Equiv_e6920ea12ba43883`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(120*t^13 - 15*t^12 - 15*t^11 - 15*t^10 - 15*t^9 - 15*t^8 - 15*t^7 - 15*t^6 - 15*t^5 - 15*t^4 - 15*t^3 - 15*t^2 - 15*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(120*t^13 - 15*t^12 - 15*t^11 - 15*t^10 - 15*t^9 - 15*t^8 - 15*t^7 - 15*t^6 - 15*t^5 - 15*t^4 - 15*t^3 - 15*t^2 - 15*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, May 30 2016 *)` (wolfram-series)
* `%O (PARI) Vec((1+x+x^2+x^3+x^4+x^5+x^6+x^7+x^8+x^9+x^10+x^11+x^12)*(1+x)/(1-15*x-15*x^2-15*x^3-15*x^4-15*x^5-15*x^6-15*x^7-15*x^8-15*x^9-15*x^10-15*x^11-15*x^12+120*x^13)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167027

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167027 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167027 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167027
