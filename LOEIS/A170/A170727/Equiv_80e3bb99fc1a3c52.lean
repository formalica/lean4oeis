import LOEIS.A170.A170727.Defs

/-!
# A170727 — program transcriptions (`Equiv_80e3bb99fc1a3c52`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^50 + 2*t^49 + 2*t^48 + 2*t^47 + 2*t^46 + 2*t^45 + 2*t^44 + 2*t^43 + 2*t^42 + 2*t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(990*t^50 - 44*t^49 - 44*t^48 - 44*t^47 - 44*t^46 - 44*t^45 - 44*t^44 - 44*t^43 - 44*t^42 - 44*t^41 - 44*t^40 - 44*t^39 - 44*t^38 - 44*t^37 - 44*t^36 - 44*t^35 - 44*t^34 - 44*t^33 - 44*t^32 - 44*t^31 - 44*t^30 - 44*t^29 - 44*t^28 - 44*t^27 - 44*t^26 - 44*t^25 - 44*t^24 - 44*t^23 - 44*t^22 - 44*t^21 - 44*t^20 - 44*t^19 - 44*t^18 - 44*t^17 - 44*t^16 - 44*t^15 - 44*t^14 - 44*t^13 - 44*t^12 - 44*t^11 - 44*t^10 - 44*t^9 - 44*t^8 - 44*t^7 - 44*t^6 - 44*t^5 - 44*t^4 - 44*t^3 - 44*t^2 - 44*t + 1). From _Zak Seidov_, Dec 04 2009: (Start) G.f.: (t^50+2f+1)/(990*t^50-44f+1) with f=t*(1+t+t^2+t^3+t^4+t^5+t^6)*(1+t^7+t^14+t^21+t^28+t^35+t^42). G.f.: (1 + t - t^50 - t^51)/(1 - 45*t + 1034*t^50 - 990*t^51). (End)` (gf-rational)
* `%T With[{num = Total[2 t^Range[49]] + t^50 + 1, den = Total[-44 t^Range[49]] + 990t^50 + 1}, CoefficientList[Series[num/den, {t, 0, 20}], t]] (* _Vincenzo Librandi_, Dec 08 2012 *)` (wolfram-series)
* `%T coxG[{50,990,-44}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170727

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170727 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A170727 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170727
