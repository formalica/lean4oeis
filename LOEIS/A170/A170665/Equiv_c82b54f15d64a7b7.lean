import LOEIS.A170.A170665.Defs

/-!
# A170665 — program transcriptions (`Equiv_c82b54f15d64a7b7`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^49 + 2*t^48 + 2*t^47 + 2*t^46 + 2*t^45 + 2*t^44 + 2*t^43 + 2*t^42 + 2*t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(465*t^49 - 30*t^48 - 30*t^47 - 30*t^46 - 30*t^45 - 30*t^44 - 30*t^43 - 30*t^42 - 30*t^41 - 30*t^40 - 30*t^39 - 30*t^38 - 30*t^37 - 30*t^36 - 30*t^35 - 30*t^34 - 30*t^33 - 30*t^32 - 30*t^31 - 30*t^30 - 30*t^29 - 30*t^28 - 30*t^27 - 30*t^26 - 30*t^25 - 30*t^24 - 30*t^23 - 30*t^22 - 30*t^21 - 30*t^20 - 30*t^19 - 30*t^18 - 30*t^17 - 30*t^16 - 30*t^15 - 30*t^14 - 30*t^13 - 30*t^12 - 30*t^11 - 30*t^10 - 30*t^9 - 30*t^8 - 30*t^7 - 30*t^6 - 30*t^5 - 30*t^4 - 30*t^3 - 30*t^2 - 30*t + 1)` (gf-rational)
* `%T With[{num=Total[2t^Range[48]]+t^49+1,den=Total[-30 t^Range[48]]+465t^49+ 1},CoefficientList[Series[num/den,{t,0,20}],t]] (* _Harvey P. Dale_, Aug 13 2014 *)` (wolfram-series)
* `%T coxG[{49,465,-30}]` (wolfram-coxG)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170665

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170665 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170665 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170665
