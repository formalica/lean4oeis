import LOEIS.A170.A170440.Defs

/-!
# A170440 — program transcriptions (`Equiv_5484df524909c25e`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^44 + 2*t^43 + 2*t^42 + 2*t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(1035*t^44 - 45*t^43 - 45*t^42 - 45*t^41 - 45*t^40 - 45*t^39 - 45*t^38 - 45*t^37 - 45*t^36 - 45*t^35 - 45*t^34 - 45*t^33 - 45*t^32 - 45*t^31 - 45*t^30 - 45*t^29 - 45*t^28 - 45*t^27 - 45*t^26 - 45*t^25 - 45*t^24 - 45*t^23 - 45*t^22 - 45*t^21 - 45*t^20 - 45*t^19 - 45*t^18 - 45*t^17 - 45*t^16 - 45*t^15 - 45*t^14 - 45*t^13 - 45*t^12 - 45*t^11 - 45*t^10 - 45*t^9 - 45*t^8 - 45*t^7 - 45*t^6 - 45*t^5 - 45*t^4 - 45*t^3 - 45*t^2 - 45*t + 1)` (gf-rational)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170440

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170440 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170440 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170440
