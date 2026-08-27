import LOEIS.A170.A170113.Defs

/-!
# A170113 — program transcriptions (`Equiv_155d1014b322c012`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(21*t^38 - 6*t^37 - 6*t^36 - 6*t^35 - 6*t^34 - 6*t^33 - 6*t^32 - 6*t^31 - 6*t^30 - 6*t^29 - 6*t^28 - 6*t^27 - 6*t^26 - 6*t^25 - 6*t^24 - 6*t^23 - 6*t^22 - 6*t^21 - 6*t^20 - 6*t^19 - 6*t^18 - 6*t^17 - 6*t^16 - 6*t^15 - 6*t^14 - 6*t^13 - 6*t^12 - 6*t^11 - 6*t^10 - 6*t^9 - 6*t^8 - 6*t^7 - 6*t^6 - 6*t^5 - 6*t^4 - 6*t^3 - 6*t^2 - 6*t + 1)` (gf-rational)
* `%T coxG[{38,21,-6}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170113

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170113 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170113 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170113
