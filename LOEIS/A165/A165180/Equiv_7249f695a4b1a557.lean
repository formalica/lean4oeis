import LOEIS.A165.A165180.Defs

/-!
# A165180 — program transcriptions (`Equiv_7249f695a4b1a557`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(1081*t^8 - 46*t^7 - 46*t^6 - 46*t^5 - 46*t^4 - 46*t^3 - 46*t^2 - 46*t + 1). a(n) = -1081*a(n-8) + 46*Sum_{k=1..7} a(n-k). - _Wesley Ivan Hurt_, Sep 04 2022` (gf-rational)
* `%F a(n) = -1081*a(n-8) + 46*Sum_{k=1..7} a(n-k). - _Wesley Ivan Hurt_, Sep 04 2022` (recurrence)
* `%T With[{num=Total[2t^Range[7]]+t^8+1,den=Total[-46 t^Range[7]]+1081t^8+ 1}, CoefficientList[Series[num/den,{t,0,30}],t]] (* _Harvey P. Dale_, Jul 27 2011 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A165180

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A165180 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A165180 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A165180
