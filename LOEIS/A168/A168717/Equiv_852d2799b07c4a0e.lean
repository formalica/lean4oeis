import LOEIS.A168.A168717.Defs

/-!
# A168717 — program transcriptions (`Equiv_852d2799b07c4a0e`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(741*t^17 - 38*t^16 - 38*t^15 - 38*t^14 - 38*t^13 - 38*t^12 - 38*t^11 - 38*t^10 - 38*t^9 - 38*t^8 - 38*t^7 - 38*t^6 - 38*t^5 - 38*t^4 - 38*t^3 - 38*t^2 - 38*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(741*t^17 - 38*t^16 - 38*t^15 - 38*t^14 - 38*t^13 - 38*t^12 - 38*t^11 - 38*t^10 - 38*t^9 - 38*t^8 - 38*t^7 - 38*t^6 - 38*t^5 - 38*t^4 - 38*t^3 - 38*t^2 - 38*t + 1), {t,0,50}], t] (* _G. C. Greubel_, Aug 05 2016 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168717

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168717 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A168717 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168717
