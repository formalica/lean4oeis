import LOEIS.A168.A168745.Defs

/-!
# A168745 — program transcriptions (`Equiv_352bcc8fd768d140`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(171*t^18 - 18*t^17 - 18*t^16 - 18*t^15 - 18*t^14 - 18*t^13 -18*t^12 - 18*t^11 - 18*t^10 - 18*t^9 - 18*t^8 - 18*t^7 - 18*t^6 - 18*t^5- 18*t^4 - 18*t^3 - 18*t^2 - 18*t + 1).` (gf-rational)
* `%T coxG[{18,171,-18}]` (wolfram-coxG)
* `%T CoefficientList[Series[(t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(171*t^18 - 18*t^17 - 18*t^16 - 18*t^15 - 18*t^14 - 18*t^13 - 18*t^12 - 18*t^11 - 18*t^10 - 18*t^9 - 18*t^8 - 18*t^7 - 18*t^6 - 18*t^5 - 18*t^4 - 18*t^3 - 18*t^2 - 18*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Aug 10 2016 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168745

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168745 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A168745 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168745
