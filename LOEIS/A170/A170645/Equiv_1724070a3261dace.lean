import LOEIS.A170.A170645.Defs

/-!
# A170645 — program transcriptions (`Equiv_1724070a3261dace`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^49 + 2*t^48 + 2*t^47 + 2*t^46 + 2*t^45 + 2*t^44 + 2*t^43 + 2*t^42 + 2*t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(55*t^49 - 10*t^48 - 10*t^47 - 10*t^46 - 10*t^45 - 10*t^44 - 10*t^43 - 10*t^42 - 10*t^41 - 10*t^40 - 10*t^39 - 10*t^38 - 10*t^37 - 10*t^36 - 10*t^35 - 10*t^34 - 10*t^33 - 10*t^32 - 10*t^31 - 10*t^30 - 10*t^29 - 10*t^28 - 10*t^27 - 10*t^26 - 10*t^25 - 10*t^24 - 10*t^23 - 10*t^22 - 10*t^21 - 10*t^20 - 10*t^19 - 10*t^18 - 10*t^17 - 10*t^16 - 10*t^15 - 10*t^14 - 10*t^13 - 10*t^12 - 10*t^11 - 10*t^10 - 10*t^9 - 10*t^8 - 10*t^7 - 10*t^6 - 10*t^5 - 10*t^4 - 10*t^3 - 10*t^2 - 10*t + 1)` (gf-rational)
* `%T With[{num=Total[2t^Range[48]]+t^49+1,den=Total[-10 t^Range[48]]+55t^49+ 1},CoefficientList[Series[num/den,{t,0,30}],t]] (* _Harvey P. Dale_, Jul 19 2014 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170645

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170645 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170645 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170645
