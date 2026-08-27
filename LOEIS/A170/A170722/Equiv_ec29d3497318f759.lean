import LOEIS.A170.A170722.Defs

/-!
# A170722 — program transcriptions (`Equiv_ec29d3497318f759`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^50 + 2*t^49 + 2*t^48 + 2*t^47 + 2*t^46 + 2*t^45 + 2*t^44 + 2*t^43 + 2*t^42 + 2*t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(780*t^50 - 39*t^49 - 39*t^48 - 39*t^47 - 39*t^46 - 39*t^45 - 39*t^44 - 39*t^43 - 39*t^42 - 39*t^41 - 39*t^40 - 39*t^39 - 39*t^38 - 39*t^37 - 39*t^36 - 39*t^35 - 39*t^34 - 39*t^33 - 39*t^32 - 39*t^31 - 39*t^30 - 39*t^29 - 39*t^28 - 39*t^27 - 39*t^26 - 39*t^25 - 39*t^24 - 39*t^23 - 39*t^22 - 39*t^21 - 39*t^20 - 39*t^19 - 39*t^18 - 39*t^17 - 39*t^16 - 39*t^15 - 39*t^14 - 39*t^13 - 39*t^12 - 39*t^11 - 39*t^10 - 39*t^9 - 39*t^8 - 39*t^7 - 39*t^6 - 39*t^5 - 39*t^4 - 39*t^3 - 39*t^2 - 39*t + 1)` (gf-rational)
* `%T With[{num = Total[2 t^Range[49]] + t^50 + 1, den = Total[-39  t^Range[49]] + 780 t^50 + 1}, CoefficientList[Series[num/den, {t, 0, 30}], t]] (* _Vincenzo Librandi_, Dec 06 2012 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170722

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 30

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 30 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170722 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 30).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 30 n h'
  have h2 : A170722 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170722
