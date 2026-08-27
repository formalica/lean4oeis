import LOEIS.A165.A165264.Defs

/-!
# A165264 — program transcriptions (`Equiv_c1f0fc92192d852a`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f. (t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(45*t^9 - 9*t^8 - 9*t^7 - 9*t^6 - 9*t^5 - 9*t^4 - 9*t^3 - 9*t^2 - 9*t + 1)` (gf-rational)
* `%T With[{num=Total[2t^Range[8]]+t^9+1,den=Total[-9 t^Range[8]]+45t^9+1}, CoefficientList[Series[num/den,{t,0,30}],t]] (* _Harvey P. Dale_, Oct 22 2011 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A165264

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A165264 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A165264 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A165264
