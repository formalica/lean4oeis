import LOEIS.A166.A166679.Defs

/-!
# A166679 — program transcriptions (`Equiv_5356831b8e7e84b7`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(496*t^12 - 31*t^11 - 31*t^10 - 31*t^9 -31*t^8 -31*t^7 -31*t^6 - 31*t^5 - 31*t^4 - 31*t^3 - 31*t^2 - 31*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(496*t^12 - 31*t^11 - 31*t^10 - 31*t^9 - 31*t^8 - 31*t^7 - 31*t^6 - 31*t^5 - 31*t^4 - 31*t^3 - 31*t^2 - 31*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, May 23 2016 *)` (wolfram-series)
* `%T coxG[{12,496,-31}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x^4+x^8)*(1+x^2)*(1+x)^2/(1-31*x-31*x^2-31*x^3-31*x^4-31*x^5-31*x^6-31*x^7-31*x^8-31*x^9-31*x^10-31*x^11+496*x^12)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166679

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166679 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A166679 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166679
