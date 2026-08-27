import LOEIS.A168.A168767.Defs

/-!
# A168767 — program transcriptions (`Equiv_3178a8f9c4759bdc`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(820*t^18 - 40*t^17 - 40*t^16 - 40*t^15 - 40*t^14 - 40*t^13 - 40*t^12 - 40*t^11 - 40*t^10 - 40*t^9 - 40*t^8 - 40*t^7 - 40*t^6 - 40*t^5 - 40*t^4 - 40*t^3 - 40*t^2 - 40*t + 1).` (gf-rational)
* `%T With[{num=Total[2t^Range[17]]+t^18+1,den=Total[-40 t^Range[17]]+ 820t^18+ 1},CoefficientList[Series[num/den,{t,0,20}],t]] (* _Harvey P. Dale_, Oct 25 2011 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168767

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168767 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A168767 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168767
