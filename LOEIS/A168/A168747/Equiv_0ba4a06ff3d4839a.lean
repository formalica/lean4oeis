import LOEIS.A168.A168747.Defs

/-!
# A168747 — program transcriptions (`Equiv_0ba4a06ff3d4839a`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(210*t^18 - 20*t^17 - 20*t^16 - 20*t^15 - 20*t^14 - 20*t^13 - 20*t^12 - 20*t^11 - 20*t^10 - 20*t^9 - 20*t^8 - 20*t^7 - 20*t^6 - 20*t^5 - 20*t^4 - 20*t^3 - 20*t^2 - 20*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(210*t^18 - 20*t^17 - 20*t^16 - 20*t^15 - 20*t^14 - 20*t^13 - 20*t^12 - 20*t^11 - 20*t^10 - 20*t^9 - 20*t^8 - 20*t^7 - 20*t^6 - 20*t^5 - 20*t^4 - 20*t^3 - 20*t^2 - 20*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Aug 10 2016 *)` (wolfram-series)
* `%T coxG[{18,210,-20}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168747

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168747 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A168747 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168747
