import LOEIS.A170.A170274.Defs

/-!
# A170274 — program transcriptions (`Equiv_9878953e1eb19312`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(276*t^41 - 23*t^40 - 23*t^39 - 23*t^38 - 23*t^37 - 23*t^36 - 23*t^35 - 23*t^34 - 23*t^33 - 23*t^32 - 23*t^31 - 23*t^30 - 23*t^29 - 23*t^28 - 23*t^27 - 23*t^26 - 23*t^25 - 23*t^24 - 23*t^23 - 23*t^22 - 23*t^21 - 23*t^20 - 23*t^19 - 23*t^18 - 23*t^17 - 23*t^16 - 23*t^15 - 23*t^14 - 23*t^13 - 23*t^12 - 23*t^11 - 23*t^10 - 23*t^9 - 23*t^8 - 23*t^7 - 23*t^6 - 23*t^5 - 23*t^4 - 23*t^3 - 23*t^2 - 23*t + 1)` (gf-rational)
* `%T coxG[{41,276,-23}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170274

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170274 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170274 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170274
