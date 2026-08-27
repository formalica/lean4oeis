import LOEIS.A168.A168803.Defs

/-!
# A168803 — program transcriptions (`Equiv_3f8016345c8715b7`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(406*t^19 - 28*t^18 - 28*t^17 - 28*t^16 - 28*t^15 - 28*t^14 - 28*t^13 - 28*t^12 - 28*t^11 - 28*t^10 - 28*t^9 - 28*t^8 - 28*t^7 - 28*t^6 - 28*t^5 - 28*t^4 - 28*t^3 - 28*t^2 - 28*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(406*t^19 - 28*t^18 - 28*t^17 - 28*t^16 - 28*t^15 - 28*t^14 - 28*t^13 - 28*t^12 - 28*t^11 - 28*t^10 - 28*t^9 - 28*t^8 - 28*t^7 - 28*t^6 - 28*t^5 - 28*t^4 - 28*t^3 - 28*t^2 - 28*t + 1), {t, 0, 500}], t] (* _G. C. Greubel_, Aug 16 2016 *)` (wolfram-series)
* `%T coxG[{19,406,-28}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168803

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 500

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 500 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168803 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 500).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 500 n h'
  have h2 : A168803 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168803
