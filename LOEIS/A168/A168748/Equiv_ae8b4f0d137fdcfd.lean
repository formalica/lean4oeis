import LOEIS.A168.A168748.Defs

/-!
# A168748 — program transcriptions (`Equiv_ae8b4f0d137fdcfd`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(231*t^18 - 21*t^17 - 21*t^16 - 21*t^15 - 21*t^14 - 21*t^13 - 21*t^12 - 21*t^11 - 21*t^10 - 21*t^9 - 21*t^8 - 21*t^7 - 21*t^6 - 21*t^5 - 21*t^4 - 21*t^3 - 21*t^2 - 21*t + 1).` (gf-rational)
* `%T With[{num=Total[2t^Range[17]]+t^18+1,den=Total[-21 t^Range[17]]+231t^18+ 1},CoefficientList[Series[num/den,{t,0,30}],t]] (* _Harvey P. Dale_, Aug 18 2013 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168748

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168748 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A168748 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168748
