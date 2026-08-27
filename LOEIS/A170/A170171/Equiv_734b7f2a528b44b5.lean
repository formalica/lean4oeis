import LOEIS.A170.A170171.Defs

/-!
# A170171 — program transcriptions (`Equiv_734b7f2a528b44b5`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(136*t^39 - 16*t^38 - 16*t^37 - 16*t^36 - 16*t^35 - 16*t^34 - 16*t^33 - 16*t^32 - 16*t^31 - 16*t^30 - 16*t^29 - 16*t^28 - 16*t^27 - 16*t^26 - 16*t^25 - 16*t^24 - 16*t^23 - 16*t^22 - 16*t^21 - 16*t^20 - 16*t^19 - 16*t^18 - 16*t^17 - 16*t^16 - 16*t^15 - 16*t^14 - 16*t^13 - 16*t^12 - 16*t^11 - 16*t^10 - 16*t^9 - 16*t^8 - 16*t^7 - 16*t^6 - 16*t^5 - 16*t^4 - 16*t^3 - 16*t^2 - 16*t + 1)` (gf-rational)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170171

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170171 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170171 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170171
