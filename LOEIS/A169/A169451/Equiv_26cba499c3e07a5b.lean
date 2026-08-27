import LOEIS.A169.A169451.Defs

/-!
# A169451 — program transcriptions (`Equiv_26cba499c3e07a5b`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(10*t^33 - 4*t^32 - 4*t^31 - 4*t^30 - 4*t^29 - 4*t^28 - 4*t^27 - 4*t^26 - 4*t^25 - 4*t^24 - 4*t^23 - 4*t^22 - 4*t^21 - 4*t^20 - 4*t^19 - 4*t^18 - 4*t^17 - 4*t^16 - 4*t^15 - 4*t^14 - 4*t^13 - 4*t^12 - 4*t^11 - 4*t^10 - 4*t^9 - 4*t^8 - 4*t^7 - 4*t^6 - 4*t^5 - 4*t^4 - 4*t^3 - 4*t^2 - 4*t + 1)` (gf-rational)
* `%T With[{num=Total[2t^Range[32]]+t^33+1,den=Total[-4 t^Range[32]]+ 10t^33+1}, CoefficientList[Series[num/den,{t,0,30}],t]] (* _Harvey P. Dale_, Apr 27 2012 *)` (wolfram-series)
* `%T coxG[{33,10,-4,30}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A169451

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A169451 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A169451 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A169451
