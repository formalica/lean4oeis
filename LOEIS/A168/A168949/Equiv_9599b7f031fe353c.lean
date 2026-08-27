import LOEIS.A168.A168949.Defs

/-!
# A168949 — program transcriptions (`Equiv_9599b7f031fe353c`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(465*t^22 - 30*t^21 - 30*t^20 - 30*t^19 - 30*t^18 - 30*t^17 - 30*t^16 - 30*t^15 - 30*t^14 - 30*t^13 - 30*t^12 - 30*t^11 - 30*t^10 - 30*t^9 - 30*t^8 - 30*t^7 - 30*t^6 - 30*t^5 - 30*t^4 - 30*t^3 - 30*t^2 - 30*t + 1).` (gf-rational)
* `%T With[{num=Total[2t^Range[21]]+t^22+1,den=Total[-30 t^Range[21]]+ 465t^22+ 1},CoefficientList[Series[num/den,{t,0,30}],t]] (* _Harvey P. Dale_, Jan 06 2013 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168949

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168949 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A168949 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168949
