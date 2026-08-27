import LOEIS.A169.A169551.Defs

/-!
# A169551 — program transcriptions (`Equiv_32f25d0b0e088bbc`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(36*t^35 - 8*t^34 - 8*t^33 - 8*t^32 - 8*t^31 - 8*t^30 - 8*t^29 - 8*t^28 - 8*t^27 - 8*t^26 - 8*t^25 - 8*t^24 - 8*t^23 - 8*t^22 - 8*t^21 - 8*t^20 - 8*t^19 - 8*t^18 - 8*t^17 - 8*t^16 - 8*t^15 - 8*t^14 - 8*t^13 - 8*t^12 - 8*t^11 - 8*t^10 - 8*t^9 - 8*t^8 - 8*t^7 - 8*t^6 - 8*t^5 - 8*t^4 - 8*t^3 - 8*t^2 - 8*t + 1)` (gf-rational)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A169551

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A169551 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A169551 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A169551
