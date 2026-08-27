import LOEIS.A168.A168963.Defs

/-!
# A168963 — program transcriptions (`Equiv_269cea3069be1da5`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(990*t^22 - 44*t^21 - 44*t^20 - 44*t^19 - 44*t^18 - 44*t^17 - 44*t^16 - 44*t^15 - 44*t^14 - 44*t^13 - 44*t^12 - 44*t^11 - 44*t^10 - 44*t^9 - 44*t^8 - 44*t^7 - 44*t^6 - 44*t^5 - 44*t^4 - 44*t^3 - 44*t^2 - 44*t + 1).` (gf-rational)
* `%T With[{num=Total[2t^Range[21]]+t^22+1,den=Total[-44 t^Range[21]]+ 990t^22+ 1},CoefficientList[Series[num/den,{t,0,30}],t]] (* _Harvey P. Dale_, Jun 06 2012 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168963

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168963 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A168963 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168963
