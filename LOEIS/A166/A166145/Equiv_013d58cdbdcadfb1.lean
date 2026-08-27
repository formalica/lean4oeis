import LOEIS.A166.A166145.Defs

/-!
# A166145 — program transcriptions (`Equiv_013d58cdbdcadfb1`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(561*t^10 - 33*t^9 - 33*t^8 - 33*t^7 - 33*t^6 - 33*t^5 - 33*t^4 - 33*t^3 - 33*t^2 - 33*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(1+t)*(1-t^10)/(1-34*t+594*t^10-561*t^11), {t, 0, 30}], t] (* _G. C. Greubel_, Apr 27 2016 *)` (wolfram-series)
* `%T coxG[{561, 10, -33}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x^2+x^4+x^6+x^8)*(1+x)^2/(1-33*x-33*x^2-33*x^3-33*x^4-33*x^5-33*x^6-33*x^7-33*x^8-33*x^9+561*x^10)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166145

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 30

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 30 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166145 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 30).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 30 n h'
  have h2 : A166145 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166145
