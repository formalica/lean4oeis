import LOEIS.A166.A166331.Defs

/-!
# A166331 — program transcriptions (`Equiv_262f1454c16cf042`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(6*t^11 - 3*t^10 - 3*t^9 - 3*t^8 - 3*t^7 - 3*t^6 - 3*t^5 - 3*t^4 - 3*t^3 - 3*t^2 - 3*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(1+t)*(1-t^11)/(1-4*t+9*t^11-6*t^12), {t,0,30}], t] (* _G. C. Greubel_, May 09 2016 *)` (wolfram-series)
* `%T coxG[{11, 6, -3}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x+x^2+x^3+x^4+x^5+x^6+x^7+x^8+x^9+x^10)*(1+x)/(1-3*x-3*x^2-3*x^3-3*x^4-3*x^5-3*x^6-3*x^7-3*x^8-3*x^9-3*x^10+6*x^11)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166331

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166331 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166331 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166331
