import LOEIS.A166.A166723.Defs

/-!
# A166723 — program transcriptions (`Equiv_b545368cc45d9265`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(903*t^12 - 42*t^11 - 42*t^10 - 42*t^9 -42*t^8 -42*t^7 -42*t^6 - 42*t^5 - 42*t^4 - 42*t^3 - 42*t^2 - 42*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(903*t^12 - 42*t^11 - 42*t^10 - 42*t^9 - 42*t^8 - 42*t^7 - 42*t^6 - 42*t^5 - 42*t^4 - 42*t^3 - 42*t^2 - 42*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, May 24 2016 *)` (wolfram-series)
* `%T coxG[{12,903,-42}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x^4+x^8)*(1+x^2)*(1+x)^2/(1-42*x-42*x^2-42*x^3-42*x^4-42*x^5-42*x^6-42*x^7-42*x^8-42*x^9-42*x^10-42*x^11+903*x^12)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166723

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166723 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A166723 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166723
