import LOEIS.A165.A165456.Defs

/-!
# A165456 — program transcriptions (`Equiv_c95a578562bf9123`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t +1)/(351*t^9 - 26*t^8 - 26*t^7 - 26*t^6 - 26*t^5 - 26*t^4 - 26*t^3 -26*t^2 - 26*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(1+t)*(1-t^9)/(1-27*t+377*t^9-351*t^10), {t, 0, 30}], t] (* _G. C. Greubel_, Oct 20 2018 *)` (wolfram-series)
* `%T coxG[{9, 351, -26}]` (wolfram-coxG)
* `%O (PARI) my(t='t+O('t^20)); Vec((1+t)*(1-t^9)/(1-27*t+377*t^9-351*t^10)) \\ _G. C. Greubel_, Oct 20 2018` (pari-vec)
* `%O (Magma) R<t>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+t)*(1-t^9)/(1-27*t+377*t^9-351*t^10) )); // _G. C. Greubel_, Oct 20 2018` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A165456

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 30

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 30 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A165456 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 30).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 30 n h'
  have h2 : A165456 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A165456
