import LOEIS.A166.A166313.Defs

/-!
# A166313 — program transcriptions (`Equiv_04dcae9856eca14f`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(1081*t^10 - 46*t^9 - 46*t^8 - 46*t^7 - 46*t^6 - 46*t^5 - 46*t^4 - 46*t^3 - 46*t^2 - 46*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(1+t)*(1-t^10)/(1-47*t+1127*t^10-1081*t^11), {t,0,30}], t] (* _G. C. Greubel_, May 09 2016 *)` (wolfram-series)
* `%T coxG[{10,1081,-46}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x^2+x^4+x^6+x^8)*(1+x)^2/(1-46*x-46*x^2-46*x^3-46*x^4-46*x^5-46*x^6-46*x^7-46*x^8-46*x^9+1081*x^10)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166313

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166313 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166313 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166313
