import LOEIS.A170.A170686.Defs

/-!
# A170686 — program transcriptions (`Equiv_1c7dc2394f5a3fc0`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^50 + 2*t^49 + 2*t^48 + 2*t^47 + 2*t^46 + 2*t^45 + 2*t^44 + 2*t^43 + 2*t^42 + 2*t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(6*t^50 - 3*t^49 - 3*t^48 - 3*t^47 - 3*t^46 - 3*t^45 - 3*t^44 - 3*t^43 - 3*t^42 - 3*t^41 - 3*t^40 - 3*t^39 - 3*t^38 - 3*t^37 - 3*t^36 - 3*t^35 - 3*t^34 - 3*t^33 - 3*t^32 - 3*t^31 - 3*t^30 - 3*t^29 - 3*t^28 - 3*t^27 - 3*t^26 - 3*t^25 - 3*t^24 - 3*t^23 - 3*t^22 - 3*t^21 - 3*t^20 - 3*t^19 - 3*t^18 - 3*t^17 - 3*t^16 - 3*t^15 - 3*t^14 - 3*t^13 - 3*t^12 - 3*t^11 - 3*t^10 - 3*t^9 - 3*t^8 - 3*t^7 - 3*t^6 - 3*t^5 - 3*t^4 - 3*t^3 - 3*t^2 - 3*t + 1).` (gf-rational)
* `%T With[{num = Total[2 t^Range[49]] + t^50 + 1, den = Total[-3 t^Range[49]] + 6 t^50 + 1}, CoefficientList[Series[num/den, {t, 0, 40}], t]] (* _Vincenzo Librandi_, Dec 09 2012 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170686

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 40

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 40 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170686 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 40).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 40 n h'
  have h2 : A170686 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170686
