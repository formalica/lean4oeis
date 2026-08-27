import LOEIS.A166.A166855.Defs

/-!
# A166855 — program transcriptions (`Equiv_6b9656a99f93fa21`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(1128*t^12 - 47*t^11 - 47*t^10 - 47*t^9 -47*t^8 -47*t^7 -47*t^6 - 47*t^5 - 47*t^4 - 47*t^3 - 47*t^2 - 47*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(1128*t^12 - 47*t^11 - 47*t^10 - 47*t^9 - 47*t^8 - 47*t^7 - 47*t^6 - 47*t^5 - 47*t^4 - 47*t^3 - 47*t^2 - 47*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, May 25 2016 *)` (wolfram-series)
* `%O (PARI) Vec((1+x^4+x^8)*(1+x^2)*(1+x)^2/(1-47*x-47*x^2-47*x^3-47*x^4-47*x^5-47*x^6-47*x^7-47*x^8-47*x^9-47*x^10-47*x^11+1128*x^12)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166855

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166855 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A166855 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166855
