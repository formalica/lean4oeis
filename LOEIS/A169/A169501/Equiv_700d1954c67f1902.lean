import LOEIS.A169.A169501.Defs

/-!
# A169501 — program transcriptions (`Equiv_700d1954c67f1902`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(21*t^34 - 6*t^33 - 6*t^32 - 6*t^31 - 6*t^30 - 6*t^29 - 6*t^28 - 6*t^27 - 6*t^26 - 6*t^25 - 6*t^24 - 6*t^23 - 6*t^22 - 6*t^21 - 6*t^20 - 6*t^19 - 6*t^18 - 6*t^17 - 6*t^16 - 6*t^15 - 6*t^14 - 6*t^13 - 6*t^12 - 6*t^11 - 6*t^10 - 6*t^9 - 6*t^8 - 6*t^7 - 6*t^6 - 6*t^5 - 6*t^4 - 6*t^3 - 6*t^2 - 6*t + 1)` (gf-rational)
* `%T With[{num=Total[2t^Range[33]]+t^34+1,den=Total[-6 t^Range[33]]+ 21t^34+ 1}, CoefficientList[Series[num/den,{t,0,30}],t]] (* _Harvey P. Dale_, Nov 05 2011 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A169501

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A169501 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A169501 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A169501
