import LOEIS.A167.A167670.Defs

/-!
# A167670 — program transcriptions (`Equiv_229d1a7a2d07849d`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(78*t^15 - 12*t^14 - 12*t^13 - 12*t^12 - 12*t^11 - 12*t^10 - 12*t^9 - 12*t^8 - 12*t^7 - 12*t^6 - 12*t^5 - 12*t^4 - 12*t^3 - 12*t^2 - 12*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(78*t^15 - 12*t^14 - 12*t^13 - 12*t^12 - 12*t^11 - 12*t^10 - 12*t^9 - 12*t^8 - 12*t^7 - 12*t^6 - 12*t^5 - 12*t^4 - 12*t^3 - 12*t^2 - 12*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Jun 19 2016 *)` (wolfram-series)
* `%T coxG[{15,78,-12}]` (wolfram-coxG)
* `%O (PARI) first(n)=Vec((1+x^5+x^10)*(1+x+x^2+x^3+x^4)*(1+x)/(1-12*x-12*x^2-12*x^3-12*x^4-12*x^5-12*x^6-12*x^7-12*x^8-12*x^9-12*x^10-12*x^11-12*x^12-12*x^13-12*x^14+78*x^15)+O(x^(n+1))) \\ _Charles R Greathouse IV_, Jun 12 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167670

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167670 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167670 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167670
