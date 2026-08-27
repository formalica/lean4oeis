import LOEIS.A164.A164670.Defs

/-!
# A164670 — program transcriptions (`Equiv_48a3c430d3b80152`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(528*t^7 - 32*t^6 - 32*t^5 - 32*t^4 - 32*t^3 - 32*t^2 - 32*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(1+t)*(1-t^7)/(1-33*t+560*t^7-528*t^8), {t, 0, 20}], t] (* _G. C. Greubel_, Sep 15 2019 *)` (wolfram-series)
* `%T coxG[{7, 528, -32}]` (wolfram-coxG)
* `%O (PARI) my(t='t+O('t^20)); Vec((1+t)*(1-t^7)/(1-33*t+560*t^7-528*t^8)) \\ _G. C. Greubel_, Sep 15 2019` (pari-vec)
* `%O (Magma) R<t>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+t)*(1-t^7)/(1-33*t+560*t^7-528*t^8) )); // _G. C. Greubel_, Sep 15 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A164670

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A164670 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A164670 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A164670
