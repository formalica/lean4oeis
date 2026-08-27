import LOEIS.A167.A167077.Defs

/-!
# A167077 — program transcriptions (`Equiv_d43f6b5ddf96ae20`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(253*t^13 - 22*t^12 - 22*t^11 - 22*t^10 - 22*t^9 - 22*t^8 - 22*t^7 - 22*t^6 - 22*t^5 - 22*t^4 - 22*t^3 - 22*t^2 - 22*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(253*t^13 - 22*t^12 - 22*t^11 - 22*t^10 - 22*t^9 - 22*t^8 - 22*t^7 - 22*t^6 - 22*t^5 - 22*t^4 - 22*t^3 - 22*t^2 - 22*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, May 31 2016 *)` (wolfram-series)
* `%T coxG[{13,253,-22}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x+x^2+x^3+x^4+x^5+x^6+x^7+x^8+x^9+x^10+x^11+x^12)*(1+x)/(1-22*x-22*x^2-22*x^3-22*x^4-22*x^5-22*x^6-22*x^7-22*x^8-22*x^9-22*x^10-22*x^11-22*x^12+253*x^13)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167077

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167077 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167077 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167077
