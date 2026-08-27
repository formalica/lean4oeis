import LOEIS.A170.A170500.Defs

/-!
# A170500 — program transcriptions (`Equiv_b0b2780f7241e66b`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^46 + 2*t^45 + 2*t^44 + 2*t^43 + 2*t^42 + 2*t^41 + 2*t^40 + 2*t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(45*t^46 - 9*t^45 - 9*t^44 - 9*t^43 - 9*t^42 - 9*t^41 - 9*t^40 - 9*t^39 - 9*t^38 - 9*t^37 - 9*t^36 - 9*t^35 - 9*t^34 - 9*t^33 - 9*t^32 - 9*t^31 - 9*t^30 - 9*t^29 - 9*t^28 - 9*t^27 - 9*t^26 - 9*t^25 - 9*t^24 - 9*t^23 - 9*t^22 - 9*t^21 - 9*t^20 - 9*t^19 - 9*t^18 - 9*t^17 - 9*t^16 - 9*t^15 - 9*t^14 - 9*t^13 - 9*t^12 - 9*t^11 - 9*t^10 - 9*t^9 - 9*t^8 - 9*t^7 - 9*t^6 - 9*t^5 - 9*t^4 - 9*t^3 - 9*t^2 - 9*t + 1)` (gf-rational)
* `%T With[{num=Total[2t^Range[45]]+t^46+1,den=Total[-9 t^Range[45]]+45t^46+ 1},CoefficientList[Series[num/den,{t,0,30}],t]] (* _Harvey P. Dale_, May 11 2014 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170500

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170500 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170500 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170500
