import LOEIS.A170.A170138.Defs

/-!
# A170138 — program transcriptions (`Equiv_04fb879c8992a340`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(496*t^38 - 31*t^37 - 31*t^36 - 31*t^35 - 31*t^34 - 31*t^33 - 31*t^32 - 31*t^31 - 31*t^30 - 31*t^29 - 31*t^28 - 31*t^27 - 31*t^26 - 31*t^25 - 31*t^24 - 31*t^23 - 31*t^22 - 31*t^21 - 31*t^20 - 31*t^19 - 31*t^18 - 31*t^17 - 31*t^16 - 31*t^15 - 31*t^14 - 31*t^13 - 31*t^12 - 31*t^11 - 31*t^10 - 31*t^9 - 31*t^8 - 31*t^7 - 31*t^6 - 31*t^5 - 31*t^4 - 31*t^3 - 31*t^2 - 31*t + 1)` (gf-rational)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170138

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170138 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170138 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170138
