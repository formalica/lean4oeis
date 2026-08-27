import LOEIS.A165.A165873.Defs

/-!
# A165873 — program transcriptions (`Equiv_0210e3fd8b51e6fa`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(66*t^10 - 11*t^9 - 11*t^8 - 11*t^7 - 11*t^6 - 11*t^5 - 11*t^4 - 11*t^3 - 11*t^2 - 11*t + 1).` (gf-rational)
* `%T coxG[{10,66,-11}]` (wolfram-coxG)
* `%T CoefficientList[Series[(1+t)*(1-t^10)/(1-12*t+77*t^10-66*t^11), {t, 0, 30}], t] (* _G. C. Greubel_, Sep 23 2019 *)` (wolfram-series)
* `%O (PARI) my(t='t+O('t^30)); Vec((1+t)*(1-t^10)/(1-12*t+77*t^10-66*t^11)) \\ _G. C. Greubel_, Sep 23 2019` (pari-vec)
* `%O (Magma) R<t>:=PowerSeriesRing(Integers(), 30); Coefficients(R!( (1+t)*(1-t^10)/(1-12*t+77*t^10-66*t^11) )); // _G. C. Greubel_, Sep 23 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A165873

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 30

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 30 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A165873 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 30).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 30 n h'
  have h2 : A165873 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A165873
