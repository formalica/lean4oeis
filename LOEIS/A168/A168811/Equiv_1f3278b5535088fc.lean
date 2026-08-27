import LOEIS.A168.A168811.Defs

/-!
# A168811 — program transcriptions (`Equiv_1f3278b5535088fc`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(666*t^19 - 36*t^18 - 36*t^17 - 36*t^16 - 36*t^15 - 36*t^14 - 36*t^13 - 36*t^12 - 36*t^11 - 36*t^10 - 36*t^9 - 36*t^8 - 36*t^7 - 36*t^6 - 36*t^5 - 36*t^4 - 36*t^3 - 36*t^2 - 36*t + 1).` (gf-rational)
* `%T coxG[{19,666,-36}]` (wolfram-coxG)
* `%T CoefficientList[Series[(t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(666*t^19 - 36*t^18 - 36*t^17 - 36*t^16 - 36*t^15 - 36*t^14 - 36*t^13 - 36*t^12 - 36*t^11 - 36*t^10 - 36*t^9 - 36*t^8 - 36*t^7 - 36*t^6 - 36*t^5 - 36*t^4 - 36*t^3 - 36*t^2 - 36*t + 1), {t, 0, 500}], t] (* _G. C. Greubel_, Aug 17 2016 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168811

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 500

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 500 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168811 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 500).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 500 n h'
  have h2 : A168811 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168811
