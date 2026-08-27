import LOEIS.A167.A167097.Defs

/-!
# A167097 — program transcriptions (`Equiv_d504e76ef1dc0ef5`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(903*t^13 - 42*t^12 - 42*t^11 - 42*t^10 - 42*t^9 - 42*t^8 - 42*t^7 - 42*t^6 - 42*t^5 - 42*t^4 - 42*t^3 - 42*t^2 - 42*t + 1).` (gf-rational)
* `%T coxG[{13,903,-42}]` (wolfram-coxG)
* `%T CoefficientList[Series[(t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(903*t^13 - 42*t^12 - 42*t^11 - 42*t^10 - 42*t^9 - 42*t^8 - 42*t^7 - 42*t^6 - 42*t^5 - 42*t^4 - 42*t^3 - 42*t^2 - 42*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Jun 02 2016 *)` (wolfram-series)
* `%O (PARI) Vec((1+x+x^2+x^3+x^4+x^5+x^6+x^7+x^8+x^9+x^10+x^11+x^12)*(1+x)/(1-42*x-42*x^2-42*x^3-42*x^4-42*x^5-42*x^6-42*x^7-42*x^8-42*x^9-42*x^10-42*x^11-42*x^12+903*x^13)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167097

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167097 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167097 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167097
