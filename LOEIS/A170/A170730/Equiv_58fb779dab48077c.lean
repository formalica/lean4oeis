import LOEIS.A170.A170730.Defs

/-!
# A170730 — program transcriptions (`Equiv_58fb779dab48077c`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^50 + 2*t^49 + 2*t^48 + 2*t^47 + 2*t^46 + 2*t^45 + 2*t^44 + 2*t^43 + 2*t^42 + 2*t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(1128*t^50 - 47*t^49 - 47*t^48 - 47*t^47 - 47*t^46 - 47*t^45 - 47*t^44 - 47*t^43 - 47*t^42 - 47*t^41 - 47*t^40 - 47*t^39 - 47*t^38 - 47*t^37 - 47*t^36 - 47*t^35 - 47*t^34 - 47*t^33 - 47*t^32 - 47*t^31 - 47*t^30 - 47*t^29 - 47*t^28 - 47*t^27 - 47*t^26 - 47*t^25 - 47*t^24 - 47*t^23 - 47*t^22 - 47*t^21 - 47*t^20 - 47*t^19 - 47*t^18 - 47*t^17 - 47*t^16 - 47*t^15 - 47*t^14 - 47*t^13 - 47*t^12 - 47*t^11 - 47*t^10 - 47*t^9 - 47*t^8 - 47*t^7 - 47*t^6 - 47*t^5 - 47*t^4 - 47*t^3 - 47*t^2 - 47*t + 1).` (gf-rational)
* `%T With[{num = Total[2 t^Range[49]] + t^50 + 1, den = Total[-47 t^Range[49]] + 1128t^50 + 1}, CoefficientList[Series[num/den, {t, 0, 200}], t]] (* _Vincenzo Librandi_, Dec 08 2012 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170730

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 200

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 200 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170730 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 200).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 200 n h'
  have h2 : A170730 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170730
