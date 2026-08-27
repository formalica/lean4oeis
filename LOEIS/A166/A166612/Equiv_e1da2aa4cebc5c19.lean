import LOEIS.A166.A166612.Defs

/-!
# A166612 — program transcriptions (`Equiv_e1da2aa4cebc5c19`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(276*t^12 - 23*t^11 - 23*t^10 - 23*t^9 -23*t^8 -23*t^7 - 23*t^6 - 23*t^5 - 23*t^4 - 23*t^3 - 23*t^2 -23*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(276*t^12 - 23*t^11 - 23*t^10 - 23*t^9 - 23*t^8 - 23*t^7 - 23*t^6 - 23*t^5 - 23*t^4 - 23*t^3 - 23*t^2 - 23*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, May 18 2016 *)` (wolfram-series)
* `%T coxG[{12,276,-23}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x^4+x^8)*(1+x^2)*(1+x)^2/(1-23*x-23*x^2-23*x^3-23*x^4-23*x^5-23*x^6-23*x^7-23*x^8-23*x^9-23*x^10-23*x^11+276*x^12)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166612

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166612 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A166612 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166612
