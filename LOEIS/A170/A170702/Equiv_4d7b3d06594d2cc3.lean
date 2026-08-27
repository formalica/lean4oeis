import LOEIS.A170.A170702.Defs

/-!
# A170702 — program transcriptions (`Equiv_4d7b3d06594d2cc3`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^50 + 2*t^49 + 2*t^48 + 2*t^47 + 2*t^46 + 2*t^45 + 2*t^44 + 2*t^43 + 2*t^42 + 2*t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(190*t^50 - 19*t^49 - 19*t^48 - 19*t^47 - 19*t^46 - 19*t^45 - 19*t^44 - 19*t^43 - 19*t^42 - 19*t^41 - 19*t^40 - 19*t^39 - 19*t^38 - 19*t^37 - 19*t^36 - 19*t^35 - 19*t^34 - 19*t^33 - 19*t^32 - 19*t^31 - 19*t^30 - 19*t^29 - 19*t^28 - 19*t^27 - 19*t^26 - 19*t^25 - 19*t^24 - 19*t^23 - 19*t^22 - 19*t^21 - 19*t^20 - 19*t^19 - 19*t^18 - 19*t^17 - 19*t^16 - 19*t^15 - 19*t^14 - 19*t^13 - 19*t^12 - 19*t^11 - 19*t^10 - 19*t^9 - 19*t^8 - 19*t^7 - 19*t^6 - 19*t^5 - 19*t^4 - 19*t^3 - 19*t^2 - 19*t + 1)` (gf-rational)
* `%T With[{num = Total[2 t^Range[49]] + t^50 + 1, den = Total[-19 t^Range[49]] + 190t^50 + 1}, CoefficientList[Series[num/den, {t, 0, 200}], t]] (* _Vincenzo Librandi_, Dec 08 2012 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170702

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 200

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 200 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170702 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 200).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 200 n h'
  have h2 : A170702 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170702
