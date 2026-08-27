import LOEIS.A166.A166328.Defs

/-!
# A166328 — program transcriptions (`Equiv_93b94aa0409ac79e`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(3*t^11 - 2*t^10 - 2*t^9 - 2*t^8 - 2*t^7 - 2*t^6 - 2*t^5 - 2*t^4 - 2*t^3 - 2*t^2 - 2*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(1+t)*(1-t^11)/(1-3*t+5*t^11-3*t^12), {t,0,30}], t] (* _G. C. Greubel_, May 09 2016 *)` (wolfram-series)
* `%T coxG[{11, 3, -2}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x+x^2+x^3+x^4+x^5+x^6+x^7+x^8+x^9+x^10)*(1+x)/(1-2*x-2*x^2-2*x^3-2*x^4-2*x^5-2*x^6-2*x^7-2*x^8-2*x^9-2*x^10+3*x^11)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166328

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166328 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166328 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166328
