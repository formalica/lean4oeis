import LOEIS.A170.A170574.Defs

/-!
# A170574 — program transcriptions (`Equiv_09fb907c6b2bd8ef`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^47 + 2*t^46 + 2*t^45 + 2*t^44 + 2*t^43 + 2*t^42 + 2*t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(630*t^47 - 35*t^46 - 35*t^45 - 35*t^44 - 35*t^43 - 35*t^42 - 35*t^41 - 35*t^40 - 35*t^39 - 35*t^38 - 35*t^37 - 35*t^36 - 35*t^35 - 35*t^34 - 35*t^33 - 35*t^32 - 35*t^31 - 35*t^30 - 35*t^29 - 35*t^28 - 35*t^27 - 35*t^26 - 35*t^25 - 35*t^24 - 35*t^23 - 35*t^22 - 35*t^21 - 35*t^20 - 35*t^19 - 35*t^18 - 35*t^17 - 35*t^16 - 35*t^15 - 35*t^14 - 35*t^13 - 35*t^12 - 35*t^11 - 35*t^10 - 35*t^9 - 35*t^8 - 35*t^7 - 35*t^6 - 35*t^5 - 35*t^4 - 35*t^3 - 35*t^2 - 35*t + 1)` (gf-rational)
* `%T coxG[{47,630,-35}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170574

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170574 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170574 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170574
