import LOEIS.A168.A168784.Defs

/-!
# A168784 — program transcriptions (`Equiv_efc22985253f38e1`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(45*t^19 - 9*t^18 - 9*t^17 - 9*t^16 - 9*t^15 - 9*t^14 - 9*t^13 - 9*t^12 - 9*t^11 - 9*t^10 - 9*t^9 - 9*t^8 - 9*t^7 - 9*t^6 - 9*t^5 - 9*t^4 - 9*t^3 - 9*t^2 - 9*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(45*t^19 - 9*t^18 - 9*t^17 - 9*t^16 - 9*t^15 - 9*t^14 - 9*t^13 - 9*t^12 - 9*t^11 - 9*t^10 - 9*t^9 - 9*t^8 - 9*t^7 - 9*t^6 - 9*t^5 - 9*t^4 - 9*t^3 - 9*t^2 - 9*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Aug 12 2016 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168784

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168784 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A168784 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168784
