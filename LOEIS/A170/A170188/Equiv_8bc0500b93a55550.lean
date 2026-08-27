import LOEIS.A170.A170188.Defs

/-!
# A170188 — program transcriptions (`Equiv_8bc0500b93a55550`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^39 + 2*t^38 + 2*t^37 + 2*t^36 + 2*t^35 + 2*t^34 + 2*t^33 + 2*t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(561*t^39 - 33*t^38 - 33*t^37 - 33*t^36 - 33*t^35 - 33*t^34 - 33*t^33 - 33*t^32 - 33*t^31 - 33*t^30 - 33*t^29 - 33*t^28 - 33*t^27 - 33*t^26 - 33*t^25 - 33*t^24 - 33*t^23 - 33*t^22 - 33*t^21 - 33*t^20 - 33*t^19 - 33*t^18 - 33*t^17 - 33*t^16 - 33*t^15 - 33*t^14 - 33*t^13 - 33*t^12 - 33*t^11 - 33*t^10 - 33*t^9 - 33*t^8 - 33*t^7 - 33*t^6 - 33*t^5 - 33*t^4 - 33*t^3 - 33*t^2 - 33*t + 1).` (gf-rational)
* `%T With[{num=Total[2t^Range[38]]+t^39+1,den=Total[-33 t^Range[38]]+561t^39+ 1},CoefficientList[Series[num/den,{t,0,20}],t]] (* _Harvey P. Dale_, Aug 26 2013 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A170188

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A170188 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A170188 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A170188
