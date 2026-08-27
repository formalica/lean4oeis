import LOEIS.A170.A170340.Defs

/-!
# A170340 — program transcriptions (`Equiv_99e9a2323e426df0`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^42 + 2*t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(861*t^42 - 41*t^41 - 41*t^40 - 41*t^39 - 41*t^38 - 41*t^37 - 41*t^36 - 41*t^35 - 41*t^34 - 41*t^33 - 41*t^32 - 41*t^31 - 41*t^30 - 41*t^29 - 41*t^28 - 41*t^27 - 41*t^26 - 41*t^25 - 41*t^24 - 41*t^23 - 41*t^22 - 41*t^21 - 41*t^20 - 41*t^19 - 41*t^18 - 41*t^17 - 41*t^16 - 41*t^15 - 41*t^14 - 41*t^13 - 41*t^12 - 41*t^11 - 41*t^10 - 41*t^9 - 41*t^8 - 41*t^7 - 41*t^6 - 41*t^5 - 41*t^4 - 41*t^3 - 41*t^2 - 41*t + 1)` (gf-rational)
* `%T coxG[{42,861,-41}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170340

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170340 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170340 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170340
