import LOEIS.A169.A169248.Defs

/-!
# A169248 — program transcriptions (`Equiv_ae6dd7d08cfd504d`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(861*t^28 - 41*t^27 - 41*t^26 - 41*t^25 - 41*t^24 - 41*t^23 - 41*t^22 - 41*t^21 - 41*t^20 - 41*t^19 - 41*t^18 - 41*t^17 - 41*t^16 - 41*t^15 - 41*t^14 - 41*t^13 - 41*t^12 - 41*t^11 - 41*t^10 - 41*t^9 - 41*t^8 - 41*t^7 - 41*t^6 - 41*t^5 - 41*t^4 - 41*t^3 - 41*t^2 - 41*t + 1).` (gf-rational)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A169248

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A169248 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A169248 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A169248
