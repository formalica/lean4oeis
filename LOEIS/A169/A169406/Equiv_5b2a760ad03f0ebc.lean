import LOEIS.A169.A169406.Defs

/-!
# A169406 — program transcriptions (`Equiv_5b2a760ad03f0ebc`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^32 + 2*t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(28*t^32 - 7*t^31 - 7*t^30 - 7*t^29 - 7*t^28 - 7*t^27 - 7*t^26 - 7*t^25 - 7*t^24 - 7*t^23 - 7*t^22 - 7*t^21 - 7*t^20 - 7*t^19 - 7*t^18 - 7*t^17 - 7*t^16 - 7*t^15 - 7*t^14 - 7*t^13 - 7*t^12 - 7*t^11 - 7*t^10 - 7*t^9 - 7*t^8 - 7*t^7 - 7*t^6 - 7*t^5 - 7*t^4 - 7*t^3 - 7*t^2 - 7*t + 1). G.f.: (1+2*sum(k=1..31, x^k)+x^32)/(1-7*sum(k=1..31, x^k)+28*x^32).` (gf-rational)
* `%T With[{num=Total[2t^Range[31]]+t^32+1,den=Total[-7 t^Range[31]]+ 28t^32+ 1}, CoefficientList[Series[num/den,{t,0,30}],t]] (* _Harvey P. Dale_, Oct 21 2011 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A169406

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A169406 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A169406 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A169406
