import LOEIS.A169.A169544.Defs

/-!
# A169544 — program transcriptions (`Equiv_3a451ef4d24e5ba2`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%T With[{num=Total[t^Range[34]]+1,den=Total[t^Range[2,34,2]]+Total[-2 t^Range[1,33,2]]+ 1},CoefficientList[Series[num/den,{t,0,40}],t]] (* _Harvey P. Dale_, May 15 2014 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A169544

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A169544 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A169544 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A169544
