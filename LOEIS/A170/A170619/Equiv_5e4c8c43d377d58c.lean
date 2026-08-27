import LOEIS.A170.A170619.Defs

/-!
# A170619 — program transcriptions (`Equiv_5e4c8c43d377d58c`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^48 + 2*t^47 + 2*t^46 + 2*t^45 + 2*t^44 + 2*t^43 + 2*t^42 + 2*t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(528*t^48 - 32*t^47 - 32*t^46 - 32*t^45 - 32*t^44 - 32*t^43 - 32*t^42 - 32*t^41 - 32*t^40 - 32*t^39 - 32*t^38 - 32*t^37 - 32*t^36 - 32*t^35 - 32*t^34 - 32*t^33 - 32*t^32 - 32*t^31 - 32*t^30 - 32*t^29 - 32*t^28 - 32*t^27 - 32*t^26 - 32*t^25 - 32*t^24 - 32*t^23 - 32*t^22 - 32*t^21 - 32*t^20 - 32*t^19 - 32*t^18 - 32*t^17 - 32*t^16 - 32*t^15 - 32*t^14 - 32*t^13 - 32*t^12 - 32*t^11 - 32*t^10 - 32*t^9 - 32*t^8 - 32*t^7 - 32*t^6 - 32*t^5 - 32*t^4 - 32*t^3 - 32*t^2 - 32*t + 1)` (gf-rational)
* `%T With[{num=Total[2t^Range[47]]+t^48+1,den=Total[-32 t^Range[47]]+ 528t^48+ 1},CoefficientList[Series[num/den,{t,0,30}],t]] (* _Harvey P. Dale_, Aug 13 2012 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170619

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170619 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170619 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170619
