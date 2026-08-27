import LOEIS.A170.A170721.Defs

/-!
# A170721 — program transcriptions (`Equiv_f80173af55d7a591`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^50 + 2*t^49 + 2*t^48 + 2*t^47 + 2*t^46 + 2*t^45 + 2*t^44 + 2*t^43 + 2*t^42 + 2*t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(741*t^50 - 38*t^49 - 38*t^48 - 38*t^47 - 38*t^46 - 38*t^45 - 38*t^44 - 38*t^43 - 38*t^42 - 38*t^41 - 38*t^40 - 38*t^39 - 38*t^38 - 38*t^37 - 38*t^36 - 38*t^35 - 38*t^34 - 38*t^33 - 38*t^32 - 38*t^31 - 38*t^30 - 38*t^29 - 38*t^28 - 38*t^27 - 38*t^26 - 38*t^25 - 38*t^24 - 38*t^23 - 38*t^22 - 38*t^21 - 38*t^20 - 38*t^19 - 38*t^18 - 38*t^17 - 38*t^16 - 38*t^15 - 38*t^14 - 38*t^13 - 38*t^12 - 38*t^11 - 38*t^10 - 38*t^9 - 38*t^8 - 38*t^7 - 38*t^6 - 38*t^5 - 38*t^4 - 38*t^3 - 38*t^2 - 38*t + 1)` (gf-rational)
* `%T With[{num = Total[2 t^Range[49]] + t^50 + 1, den = Total[-38  t^Range[49]] + 741 t^50 + 1}, CoefficientList[Series[num/den, {t, 0, 30}], t]] (* _Vincenzo Librandi_, Dec 06 2012 *)` (wolfram-series)
* `%T coxG[{50,741,-38}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170721

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 30

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 30 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170721 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 30).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 30 n h'
  have h2 : A170721 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170721
