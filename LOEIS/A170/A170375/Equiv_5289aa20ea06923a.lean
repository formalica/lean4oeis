import LOEIS.A170.A170375.Defs

/-!
# A170375 — program transcriptions (`Equiv_5289aa20ea06923a`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^43 + 2*t^42 + 2*t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(406*t^43 - 28*t^42 - 28*t^41 - 28*t^40 - 28*t^39 - 28*t^38 - 28*t^37 - 28*t^36 - 28*t^35 - 28*t^34 - 28*t^33 - 28*t^32 - 28*t^31 - 28*t^30 - 28*t^29 - 28*t^28 - 28*t^27 - 28*t^26 - 28*t^25 - 28*t^24 - 28*t^23 - 28*t^22 - 28*t^21 - 28*t^20 - 28*t^19 - 28*t^18 - 28*t^17 - 28*t^16 - 28*t^15 - 28*t^14 - 28*t^13 - 28*t^12 - 28*t^11 - 28*t^10 - 28*t^9 - 28*t^8 - 28*t^7 - 28*t^6 - 28*t^5 - 28*t^4 - 28*t^3 - 28*t^2 - 28*t + 1)` (gf-rational)
* `%T coxG[{43,406,-28}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170375

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170375 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170375 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170375
