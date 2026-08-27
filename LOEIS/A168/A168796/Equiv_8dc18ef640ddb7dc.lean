import LOEIS.A168.A168796.Defs

/-!
# A168796 — program transcriptions (`Equiv_8dc18ef640ddb7dc`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(231*t^19 - 21*t^18 - 21*t^17 - 21*t^16 - 21*t^15 - 21*t^14 - 21*t^13 - 21*t^12 - 21*t^11 - 21*t^10 - 21*t^9 - 21*t^8 - 21*t^7 - 21*t^6 - 21*t^5 - 21*t^4 - 21*t^3 - 21*t^2 - 21*t + 1).` (gf-rational)
* `%T coxG[{19,231,-21}]` (wolfram-coxG)
* `%T CoefficientList[Series[(t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(231*t^19 - 21*t^18 - 21*t^17 - 21*t^16 - 21*t^15 - 21*t^14 - 21*t^13 - 21*t^12 - 21*t^11 - 21*t^10 - 21*t^9 - 21*t^8 - 21*t^7 - 21*t^6 - 21*t^5 - 21*t^4 - 21*t^3 - 21*t^2 - 21*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Aug 15 2016 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168796

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168796 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A168796 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168796
