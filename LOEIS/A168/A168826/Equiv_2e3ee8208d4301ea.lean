import LOEIS.A168.A168826.Defs

/-!
# A168826 — program transcriptions (`Equiv_2e3ee8208d4301ea`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(6*t^20 - 3*t^19 - 3*t^18 - 3*t^17 - 3*t^16 - 3*t^15 - 3*t^14 - 3*t^13 - 3*t^12 - 3*t^11 - 3*t^10 - 3*t^9 - 3*t^8 - 3*t^7 - 3*t^6 - 3*t^5 - 3*t^4 - 3*t^3 - 3*t^2 - 3*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(6*t^20 - 3*t^19 - 3*t^18 - 3*t^17 - 3*t^16 - 3*t^15 - 3*t^14 - 3*t^13 - 3*t^12 - 3*t^11 - 3*t^10 - 3*t^9 - 3*t^8 - 3*t^7 - 3*t^6 - 3*t^5 - 3*t^4 - 3*t^3 - 3*t^2 - 3*t + 1), {t,0,100}], t] (* _G. C. Greubel_, Nov 22 2016 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168826

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168826 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A168826 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168826
