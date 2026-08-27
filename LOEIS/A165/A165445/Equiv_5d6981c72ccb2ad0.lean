import LOEIS.A165.A165445.Defs

/-!
# A165445 — program transcriptions (`Equiv_5d6981c72ccb2ad0`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(325*t^9 - 25*t^8 - 25*t^7 - 25*t^6 - 25*t^5 - 25*t^4 - 25*t^3 - 25*t^2 - 25*t + 1).` (gf-rational)
* `%T coxG[{9,325,-25}]` (wolfram-coxG)
* `%T CoefficientList[Series[(1+t)*(1-t^9)/(1-26*t+350*t^9-325*t^10), {t, 0, 20}], t] (* _G. C. Greubel_, Oct 20 2018 *)` (wolfram-series)
* `%O (PARI) t='t+O('t^20); Vec((1+t)*(1-t^9)/(1-26*t+350*t^9-325*t^10)) \\ _G. C. Greubel_, Oct 20 2018` (pari-vec)
* `%O (Magma) R<t>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+t)*(1-t^9)/(1-26*t+350*t^9-325*t^10) )); // _G. C. Greubel_, Oct 20 2018` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A165445

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A165445 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A165445 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A165445
