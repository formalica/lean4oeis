import LOEIS.A168.A168801.Defs

/-!
# A168801 — program transcriptions (`Equiv_1e152b319dc85891`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(351*t^19 - 26*t^18 - 26*t^17 - 26*t^16 - 26*t^15 - 26*t^14 - 26*t^13 - 26*t^12 - 26*t^11 - 26*t^10 - 26*t^9 - 26*t^8 - 26*t^7 - 26*t^6 - 26*t^5 - 26*t^4 - 26*t^3 - 26*t^2 - 26*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(351*t^19 - 26*t^18 - 26*t^17 - 26*t^16 - 26*t^15 - 26*t^14 - 26*t^13 - 26*t^12 - 26*t^11 - 26*t^10 - 26*t^9 - 26*t^8 - 26*t^7 - 26*t^6 - 26*t^5 - 26*t^4 - 26*t^3 - 26*t^2 - 26*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Aug 16 2016 *)` (wolfram-series)
* `%T coxG[{19,351,-26}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168801

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168801 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A168801 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168801
