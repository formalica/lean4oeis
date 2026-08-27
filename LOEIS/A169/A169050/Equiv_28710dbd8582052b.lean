import LOEIS.A169.A169050.Defs

/-!
# A169050 — program transcriptions (`Equiv_28710dbd8582052b`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(630*t^24 - 35*t^23 - 35*t^22 - 35*t^21 - 35*t^20 - 35*t^19 - 35*t^18 - 35*t^17 - 35*t^16 - 35*t^15 - 35*t^14 - 35*t^13 - 35*t^12 - 35*t^11 - 35*t^10 - 35*t^9 - 35*t^8 - 35*t^7 - 35*t^6 - 35*t^5 - 35*t^4 - 35*t^3 - 35*t^2 - 35*t + 1).` (gf-rational)
* `%T With[{num=Total[2t^Range[23]]+t^24+1,den=Total[-35 t^Range[23]]+630t^24+ 1}, CoefficientList[Series[num/den,{t,0,30}],t]] (* _Harvey P. Dale_, Dec 12 2011 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A169050

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A169050 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A169050 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A169050
