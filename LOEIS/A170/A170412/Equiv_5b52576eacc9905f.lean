import LOEIS.A170.A170412.Defs

/-!
# A170412 — program transcriptions (`Equiv_5b52576eacc9905f`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^44 + 2*t^43 + 2*t^42 + 2*t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(153*t^44 - 17*t^43 - 17*t^42 - 17*t^41 - 17*t^40 - 17*t^39 - 17*t^38 - 17*t^37 - 17*t^36 - 17*t^35 - 17*t^34 - 17*t^33 - 17*t^32 - 17*t^31 - 17*t^30 - 17*t^29 - 17*t^28 - 17*t^27 - 17*t^26 - 17*t^25 - 17*t^24 - 17*t^23 - 17*t^22 - 17*t^21 - 17*t^20 - 17*t^19 - 17*t^18 - 17*t^17 - 17*t^16 - 17*t^15 - 17*t^14 - 17*t^13 - 17*t^12 - 17*t^11 - 17*t^10 - 17*t^9 - 17*t^8 - 17*t^7 - 17*t^6 - 17*t^5 - 17*t^4 - 17*t^3 - 17*t^2 - 17*t + 1)` (gf-rational)
* `%T coxG[{44,153,-17}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170412

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170412 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170412 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170412
