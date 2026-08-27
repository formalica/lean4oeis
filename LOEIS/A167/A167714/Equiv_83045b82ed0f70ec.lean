import LOEIS.A167.A167714.Defs

/-!
# A167714 — program transcriptions (`Equiv_83045b82ed0f70ec`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(378*t^15 - 27*t^14 - 27*t^13 - 27*t^12 - 27*t^11 - 27*t^10 - 27*t^9 - 27*t^8 - 27*t^7 - 27*t^6 - 27*t^5 - 27*t^4 - 27*t^3 - 27*t^2 - 27*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(378*t^15 - 27*t^14 - 27*t^13 - 27*t^12 - 27*t^11 - 27*t^10 - 27*t^9 - 27*t^8 - 27*t^7 - 27*t^6 - 27*t^5 - 27*t^4 - 27*t^3 - 27*t^2 - 27*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Jun 20 2016 *)` (wolfram-series)
* `%T coxG[{15,378,-27}]` (wolfram-coxG)
* `%O (PARI) first(n)=Vec((1+x^5+x^10)*(1+x+x^2+x^3+x^4)*(1+x)/(1-27*x-27*x^2-27*x^3-27*x^4-27*x^5-27*x^6-27*x^7-27*x^8-27*x^9-27*x^10-27*x^11-27*x^12-27*x^13-27*x^14+378*x^15)+O(x^(n+1))) \\ _Charles R Greathouse IV_, Jun 13 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167714

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167714 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167714 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167714
