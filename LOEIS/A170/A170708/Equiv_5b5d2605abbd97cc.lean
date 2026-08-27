import LOEIS.A170.A170708.Defs

/-!
# A170708 — program transcriptions (`Equiv_5b5d2605abbd97cc`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^50 + 2*t^49 + 2*t^48 + 2*t^47 + 2*t^46 + 2*t^45 + 2*t^44 + 2*t^43 + ,2*t^42 + 2*t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + ,2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + ,2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + ,2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + ,2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + ,2*t + 1)/(325*t^50 - 25*t^49 - 25*t^48 - 25*t^47 - 25*t^46 - 25*t^45 - ,25*t^44 - 25*t^43 - 25*t^42 - 25*t^41 - 25*t^40 - 25*t^39 - 25*t^38 - ,25*t^37 - 25*t^36 - 25*t^35 - 25*t^34 - 25*t^33 - 25*t^32 - 25*t^31 - ,25*t^30 - 25*t^29 - 25*t^28 - 25*t^27 - 25*t^26 - 25*t^25 - 25*t^24 - ,25*t^23 - 25*t^22 - 25*t^21 - 25*t^20 - 25*t^19 - 25*t^18 - 25*t^17 - ,25*t^16 - 25*t^15 - 25*t^14 - 25*t^13 - 25*t^12 - 25*t^11 - 25*t^10 - ,25*t^9 - 25*t^8 - 25*t^7 - 25*t^6 - 25*t^5 - 25*t^4 - 25*t^3 - 25*t^2 - ,25*t + 1).` (gf-rational)
* `%T With[{num = Total[2 t^Range[49]] + t^50 + 1, den = Total[-25 t^Range[49]] + 325 t^50 + 1}, CoefficientList[Series[num/den, {t, 0, 30}], t]] (* _Vincenzo Librandi_, Dec 06 2012 *)` (wolfram-series)
* `%T coxG[{50,325,-25}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170708

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 30

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 30 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170708 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 30).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 30 n h'
  have h2 : A170708 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170708
