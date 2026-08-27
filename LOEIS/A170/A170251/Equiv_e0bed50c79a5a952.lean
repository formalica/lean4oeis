import LOEIS.A170.A170251.Defs

/-!
# A170251 — program transcriptions (`Equiv_e0bed50c79a5a952`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(1176*t^40 - 48*t^39 - 48*t^38 - 48*t^37 - 48*t^36 - 48*t^35 - 48*t^34 - 48*t^33 - 48*t^32 - 48*t^31 - 48*t^30 - 48*t^29 - 48*t^28 - 48*t^27 - 48*t^26 - 48*t^25 - 48*t^24 - 48*t^23 - 48*t^22 - 48*t^21 - 48*t^20 - 48*t^19 - 48*t^18 - 48*t^17 - 48*t^16 - 48*t^15 - 48*t^14 - 48*t^13 - 48*t^12 - 48*t^11 - 48*t^10 - 48*t^9 - 48*t^8 - 48*t^7 - 48*t^6 - 48*t^5 - 48*t^4 - 48*t^3 - 48*t^2 - 48*t + 1)` (gf-rational)
* `%T With[{num=Total[2t^Range[39]]+t^40+1,den=Total[-48 t^Range[39]]+ 1176t^40+ 1},CoefficientList[Series[num/den,{t,0,30}],t]] (* _Harvey P. Dale_, Dec 23 2012 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170251

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170251 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170251 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170251
