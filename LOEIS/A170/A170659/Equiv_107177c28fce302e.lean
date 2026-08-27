import LOEIS.A170.A170659.Defs

/-!
# A170659 — program transcriptions (`Equiv_107177c28fce302e`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^49 + 2*t^48 + 2*t^47 + 2*t^46 + 2*t^45 + 2*t^44 + 2*t^43 + 2*t^42 + 2*t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(300*t^49 - 24*t^48 - 24*t^47 - 24*t^46 - 24*t^45 - 24*t^44 - 24*t^43 - 24*t^42 - 24*t^41 - 24*t^40 - 24*t^39 - 24*t^38 - 24*t^37 - 24*t^36 - 24*t^35 - 24*t^34 - 24*t^33 - 24*t^32 - 24*t^31 - 24*t^30 - 24*t^29 - 24*t^28 - 24*t^27 - 24*t^26 - 24*t^25 - 24*t^24 - 24*t^23 - 24*t^22 - 24*t^21 - 24*t^20 - 24*t^19 - 24*t^18 - 24*t^17 - 24*t^16 - 24*t^15 - 24*t^14 - 24*t^13 - 24*t^12 - 24*t^11 - 24*t^10 - 24*t^9 - 24*t^8 - 24*t^7 - 24*t^6 - 24*t^5 - 24*t^4 - 24*t^3 - 24*t^2 - 24*t + 1)` (gf-rational)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170659

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170659 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170659 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170659
