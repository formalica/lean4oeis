import LOEIS.A168.A168742.Defs

/-!
# A168742 — program transcriptions (`Equiv_a7a21227142f32c4`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(120*t^18 - 15*t^17 - 15*t^16 - 15*t^15 - 15*t^14 - 15*t^13 - 15*t^12 - 15*t^11 - 15*t^10 - 15*t^9 - 15*t^8 - 15*t^7 - 15*t^6 - 15*t^5 - 15*t^4 - 15*t^3 - 15*t^2 - 15*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(120*t^18 - 15*t^17 - 15*t^16 - 15*t^15 - 15*t^14 - 15*t^13 - 15*t^12 - 15*t^11 - 15*t^10 - 15*t^9 - 15*t^8 - 15*t^7 - 15*t^6 - 15*t^5 - 15*t^4 - 15*t^3 - 15*t^2 - 15*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Aug 10 2016 *)` (wolfram-series)
* `%T coxG[{18,120,-15}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168742

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168742 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A168742 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168742
