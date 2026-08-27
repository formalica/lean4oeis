import LOEIS.A167.A167651.Defs

/-!
# A167651 — program transcriptions (`Equiv_b3438673adfadf35`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(10*t^15 - 4*t^14 - 4*t^13 - 4*t^12 - 4*t^11 - 4*t^10 - 4*t^9 - 4*t^8 - 4*t^7 - 4*t^6 - 4*t^5 - 4*t^4 - 4*t^3 - 4*t^2 - 4*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(10*t^15 - 4*t^14 - 4*t^13 - 4*t^12 - 4*t^11 - 4*t^10 - 4*t^9 - 4*t^8 - 4*t^7 - 4*t^6 - 4*t^5 - 4*t^4 - 4*t^3 - 4*t^2 - 4*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Jun 18 2016 *)` (wolfram-series)
* `%O (PARI) first(n)=Vec((1+x^5+x^10)*(1+x+x^2+x^3+x^4)*(1+x)/(1-4*x-4*x^2-4*x^3-4*x^4-4*x^5-4*x^6-4*x^7-4*x^8-4*x^9-4*x^10-4*x^11-4*x^12-4*x^13-4*x^14+10*x^15)+O(x^(n+1))) \\ _Charles R Greathouse IV_, Jun 12 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167651

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167651 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167651 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167651
