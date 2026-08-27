import LOEIS.A170.A170709.Defs

/-!
# A170709 — program transcriptions (`Equiv_387936c34850e2b9`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^50 + 2*t^49 + 2*t^48 + 2*t^47 + 2*t^46 + 2*t^45 + 2*t^44 + 2*t^43 + 2*t^42 + 2*t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(351*t^50 - 26*t^49 - 26*t^48 - 26*t^47 - 26*t^46 - 26*t^45 - 26*t^44 - 26*t^43 - 26*t^42 - 26*t^41 - 26*t^40 - 26*t^39 - 26*t^38 - 26*t^37 - 26*t^36 - 26*t^35 - 26*t^34 - 26*t^33 - 26*t^32 - 26*t^31 - 26*t^30 - 26*t^29 - 26*t^28 - 26*t^27 - 26*t^26 - 26*t^25 - 26*t^24 - 26*t^23 - 26*t^22 - 26*t^21 - 26*t^20 - 26*t^19 - 26*t^18 - 26*t^17 - 26*t^16 - 26*t^15 - 26*t^14 - 26*t^13 - 26*t^12 - 26*t^11 - 26*t^10 - 26*t^9 - 26*t^8 - 26*t^7 - 26*t^6 - 26*t^5 - 26*t^4 - 26*t^3 - 26*t^2 - 26*t + 1).` (gf-rational)
* `%T With[{num = Total[2 t^Range[49]] + t^50 + 1, den = Total[-26 t^Range[49]] + 351 t^50 + 1}, CoefficientList[Series[num/den, {t, 0, 30}], t]] (* _Vincenzo Librandi_, Dec 06 2012 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170709

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 30

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 30 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170709 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 30).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 30 n h'
  have h2 : A170709 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170709
