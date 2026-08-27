import LOEIS.A170.A170073.Defs

/-!
# A170073 — program transcriptions (`Equiv_6e957218882faf39`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(105*t^37 - 14*t^36 - 14*t^35 - 14*t^34 - 14*t^33 - 14*t^32 - 14*t^31 - 14*t^30 - 14*t^29 - 14*t^28 - 14*t^27 - 14*t^26 - 14*t^25 - 14*t^24 - 14*t^23 - 14*t^22 - 14*t^21 - 14*t^20 - 14*t^19 - 14*t^18 - 14*t^17 - 14*t^16 - 14*t^15 - 14*t^14 - 14*t^13 - 14*t^12 - 14*t^11 - 14*t^10 - 14*t^9 - 14*t^8 - 14*t^7 - 14*t^6 - 14*t^5 - 14*t^4 - 14*t^3 - 14*t^2 - 14*t + 1)` (gf-rational)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170073

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170073 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170073 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170073
