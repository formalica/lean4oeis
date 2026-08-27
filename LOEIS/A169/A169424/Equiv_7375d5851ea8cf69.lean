import LOEIS.A169.A169424.Defs

/-!
# A169424 — program transcriptions (`Equiv_7375d5851ea8cf69`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(325*t^32 - 25*t^31 - 25*t^30 - 25*t^29 - 25*t^28 - 25*t^27 - 25*t^26 - 25*t^25 - 25*t^24 - 25*t^23 - 25*t^22 - 25*t^21 - 25*t^20 - 25*t^19 - 25*t^18 - 25*t^17 - 25*t^16 - 25*t^15 - 25*t^14 - 25*t^13 - 25*t^12 - 25*t^11 - 25*t^10 - 25*t^9 - 25*t^8 - 25*t^7 - 25*t^6 - 25*t^5 - 25*t^4 - 25*t^3 - 25*t^2 - 25*t + 1). G.f.: (1+2*sum(k=1..31, x^k)+x^32)/(1-25*sum(k=1..31, x^k)+325*x^32).` (gf-rational)
* `%T With[{num=Total[2t^Range[31]]+t^32+1,den=Total[-25 t^Range[31]]+ 325t^32+ 1}, CoefficientList[Series[num/den,{t,0,30}],t]]  (* _Harvey P. Dale_, Jun 18 2012 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A169424

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A169424 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A169424 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A169424
