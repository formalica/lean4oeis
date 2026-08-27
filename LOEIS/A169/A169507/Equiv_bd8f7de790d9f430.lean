import LOEIS.A169.A169507.Defs

/-!
# A169507 — program transcriptions (`Equiv_bd8f7de790d9f430`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(78*t^34 - 12*t^33 - 12*t^32 - 12*t^31 - 12*t^30 - 12*t^29 - 12*t^28 - 12*t^27 - 12*t^26 - 12*t^25 - 12*t^24 - 12*t^23 - 12*t^22 - 12*t^21 - 12*t^20 - 12*t^19 - 12*t^18 - 12*t^17 - 12*t^16 - 12*t^15 - 12*t^14 - 12*t^13 - 12*t^12 - 12*t^11 - 12*t^10 - 12*t^9 - 12*t^8 - 12*t^7 - 12*t^6 - 12*t^5 - 12*t^4 - 12*t^3 - 12*t^2 - 12*t + 1)` (gf-rational)
* `%T coxG[{34,78,-12}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A169507

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A169507 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A169507 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A169507
