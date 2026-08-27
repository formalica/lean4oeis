import LOEIS.A165.A165515.Defs

/-!
# A165515 — program transcriptions (`Equiv_9429a5ac884d8663`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^9 +2*t^8 +2*t^7 +2*t^6 +2*t^5 +2*t^4 +2*t^3 +2*t^2 +2*t +1)/( 406*t^9 -28*t^8 -28*t^7 -28*t^6 -28*t^5 -28*t^4 -28*t^3 -28*t^2 -28*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(1+t)*(1-t^9)/(1-29*t+434*t^9-406*t^10), {t,0,20}], t] (* _G. C. Greubel_, Oct 21 2018 *)` (wolfram-series)
* `%T coxG[{9, 406, -28}]` (wolfram-coxG)
* `%O (PARI) my(t='t+O('t^20)); Vec((1+t)*(1-t^9)/(1-29*t+434*t^9-406*t^10)) \\ _G. C. Greubel_, Oct 21 2018` (pari-vec)
* `%O (Magma) R<t>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+t)*(1-t^9)/(1-29*t+434*t^9-406*t^10) )); // _G. C. Greubel_, Oct 21 2018` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A165515

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A165515 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A165515 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A165515
