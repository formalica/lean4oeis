import LOEIS.A170.A170537.Defs

/-!
# A170537 — program transcriptions (`Equiv_31853f56407257a6`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^46 + 2*t^45 + 2*t^44 + 2*t^43 + 2*t^42 + 2*t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(1081*t^46 - 46*t^45 - 46*t^44 - 46*t^43 - 46*t^42 - 46*t^41 - 46*t^40 - 46*t^39 - 46*t^38 - 46*t^37 - 46*t^36 - 46*t^35 - 46*t^34 - 46*t^33 - 46*t^32 - 46*t^31 - 46*t^30 - 46*t^29 - 46*t^28 - 46*t^27 - 46*t^26 - 46*t^25 - 46*t^24 - 46*t^23 - 46*t^22 - 46*t^21 - 46*t^20 - 46*t^19 - 46*t^18 - 46*t^17 - 46*t^16 - 46*t^15 - 46*t^14 - 46*t^13 - 46*t^12 - 46*t^11 - 46*t^10 - 46*t^9 - 46*t^8 - 46*t^7 - 46*t^6 - 46*t^5 - 46*t^4 - 46*t^3 - 46*t^2 - 46*t + 1)` (gf-rational)
* `%T coxG[{46,1081,-46}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170537

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170537 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170537 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170537
