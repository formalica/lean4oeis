import LOEIS.A169.A169133.Defs

/-!
# A169133 — program transcriptions (`Equiv_dc1e8c20c9205a41`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(253*t^26 - 22*t^25 - 22*t^24 - 22*t^23 - 22*t^22 - 22*t^21 - 22*t^20 - 22*t^19 - 22*t^18 - 22*t^17 - 22*t^16 - 22*t^15 - 22*t^14 - 22*t^13 - 22*t^12 - 22*t^11 - 22*t^10 - 22*t^9 - 22*t^8 - 22*t^7 - 22*t^6 - 22*t^5 - 22*t^4 - 22*t^3 - 22*t^2 - 22*t + 1).` (gf-rational)
* `%T With[{num=Total[2t^Range[25]]+t^26+1,den=Total[-22 t^Range[25]]+ 253t^26+1}, CoefficientList[Series[num/den,{t,0,30}],t]] (* _Harvey P. Dale_, Feb 27 2012 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A169133

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A169133 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A169133 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A169133
