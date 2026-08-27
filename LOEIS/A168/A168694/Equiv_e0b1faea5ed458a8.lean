import LOEIS.A168.A168694.Defs

/-!
# A168694 — program transcriptions (`Equiv_e0b1faea5ed458a8`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/ (120*t^17 - 15*t^16 - 15*t^15 - 15*t^14 - 15*t^13 - 15*t^12 - 15*t^11 - 15*t^10 - 15*t^9 - 15*t^8 - 15*t^7 - 15*t^6 - 15*t^5 - 15*t^4 - 15*t^3 - 15*t^2 - 15*t + 1).` (gf-rational)
* `%T With[{num=Total[2t^Range[16]]+t^17+1,den=Total[-15 t^Range[16]]+ 120t^17+ 1},CoefficientList[Series[num/den,{t,0,30}],t]] (* _Harvey P. Dale_, Jun 04 2012 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168694

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168694 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A168694 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168694
