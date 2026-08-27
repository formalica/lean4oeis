import LOEIS.A170.A170033.Defs

/-!
# A170033 — program transcriptions (`Equiv_603bd4f89b9d5b8b`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(253*t^36 - 22*t^35 - 22*t^34 - 22*t^33 - 22*t^32 - 22*t^31 - 22*t^30 - 22*t^29 - 22*t^28 - 22*t^27 - 22*t^26 - 22*t^25 - 22*t^24 - 22*t^23 - 22*t^22 - 22*t^21 - 22*t^20 - 22*t^19 - 22*t^18 - 22*t^17 - 22*t^16 - 22*t^15 - 22*t^14 - 22*t^13 - 22*t^12 - 22*t^11 - 22*t^10 - 22*t^9 - 22*t^8 - 22*t^7 - 22*t^6 - 22*t^5 - 22*t^4 - 22*t^3 - 22*t^2 - 22*t + 1)` (gf-rational)
* `%T With[{num=Total[2t^Range[35]]+t^36+1,den=Total[-22 t^Range[35]]+ 253t^36+ 1}, CoefficientList[Series[num/den,{t,0,20}],t]] (* _Harvey P. Dale_, Nov 16 2011 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170033

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170033 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170033 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170033
