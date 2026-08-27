import LOEIS.A170.A170263.Defs

/-!
# A170263 — program transcriptions (`Equiv_2e23e98d5a3fd956`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(78*t^41 - 12*t^40 - 12*t^39 - 12*t^38 - 12*t^37 - 12*t^36 - 12*t^35 - 12*t^34 - 12*t^33 - 12*t^32 - 12*t^31 - 12*t^30 - 12*t^29 - 12*t^28 - 12*t^27 - 12*t^26 - 12*t^25 - 12*t^24 - 12*t^23 - 12*t^22 - 12*t^21 - 12*t^20 - 12*t^19 - 12*t^18 - 12*t^17 - 12*t^16 - 12*t^15 - 12*t^14 - 12*t^13 - 12*t^12 - 12*t^11 - 12*t^10 - 12*t^9 - 12*t^8 - 12*t^7 - 12*t^6 - 12*t^5 - 12*t^4 - 12*t^3 - 12*t^2 - 12*t + 1)` (gf-rational)
* `%T With[{num=Total[2t^Range[40]]+t^41+1,den=Total[-12 t^Range[40]]+78t^41+ 1},CoefficientList[Series[num/den,{t,0,30}],t]] (* _Harvey P. Dale_, Dec 17 2013 *)` (wolfram-series)
* `%T coxG[{41,78,-12}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170263

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170263 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170263 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170263
