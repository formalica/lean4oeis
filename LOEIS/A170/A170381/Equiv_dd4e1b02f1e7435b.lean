import LOEIS.A170.A170381.Defs

/-!
# A170381 — program transcriptions (`Equiv_dd4e1b02f1e7435b`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^43 + 2*t^42 + 2*t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(595*t^43 - 34*t^42 - 34*t^41 - 34*t^40 - 34*t^39 - 34*t^38 - 34*t^37 - 34*t^36 - 34*t^35 - 34*t^34 - 34*t^33 - 34*t^32 - 34*t^31 - 34*t^30 - 34*t^29 - 34*t^28 - 34*t^27 - 34*t^26 - 34*t^25 - 34*t^24 - 34*t^23 - 34*t^22 - 34*t^21 - 34*t^20 - 34*t^19 - 34*t^18 - 34*t^17 - 34*t^16 - 34*t^15 - 34*t^14 - 34*t^13 - 34*t^12 - 34*t^11 - 34*t^10 - 34*t^9 - 34*t^8 - 34*t^7 - 34*t^6 - 34*t^5 - 34*t^4 - 34*t^3 - 34*t^2 - 34*t + 1)` (gf-rational)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170381

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170381 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170381 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170381
