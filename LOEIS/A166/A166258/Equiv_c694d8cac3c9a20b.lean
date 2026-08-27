import LOEIS.A166.A166258.Defs

/-!
# A166258 — program transcriptions (`Equiv_c694d8cac3c9a20b`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(946*t^10 - 43*t^9 - 43*t^8 - 43*t^7 - 43*t^6 - 43*t^5 - 43*t^4 - 43*t^3 - 43*t^2 - 43*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(1+t)*(1-t^10)/(1-44*t+989*t^10-946*t^11), {t,0,30}], t] (* _G. C. Greubel_, May 08 2016 *)` (wolfram-series)
* `%T coxG[{10, 946, -43}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x^2+x^4+x^6+x^8)*(1+x)^2/(1-43*x-43*x^2-43*x^3-43*x^4-43*x^5-43*x^6-43*x^7-43*x^8-43*x^9+946*x^10)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166258

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166258 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166258 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166258
