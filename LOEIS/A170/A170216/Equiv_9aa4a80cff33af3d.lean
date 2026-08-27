import LOEIS.A170.A170216.Defs

/-!
# A170216 — program transcriptions (`Equiv_9aa4a80cff33af3d`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(91*t^40 - 13*t^39 - 13*t^38 - 13*t^37 - 13*t^36 - 13*t^35 - 13*t^34 - 13*t^33 - 13*t^32 - 13*t^31 - 13*t^30 - 13*t^29 - 13*t^28 - 13*t^27 - 13*t^26 - 13*t^25 - 13*t^24 - 13*t^23 - 13*t^22 - 13*t^21 - 13*t^20 - 13*t^19 - 13*t^18 - 13*t^17 - 13*t^16 - 13*t^15 - 13*t^14 - 13*t^13 - 13*t^12 - 13*t^11 - 13*t^10 - 13*t^9 - 13*t^8 - 13*t^7 - 13*t^6 - 13*t^5 - 13*t^4 - 13*t^3 - 13*t^2 - 13*t + 1)` (gf-rational)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170216

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170216 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170216 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170216
