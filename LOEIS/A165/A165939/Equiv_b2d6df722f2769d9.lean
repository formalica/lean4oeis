import LOEIS.A165.A165939.Defs

/-!
# A165939 — program transcriptions (`Equiv_b2d6df722f2769d9`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(231*t^10 - 21*t^9 - 21*t^8 - 21*t^7 - 21*t^6 - 21*t^5 - 21*t^4 - 21*t^3 - 21*t^2 - 21*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(1+t)*(1-t^10)/(1-22*t+252*t^10-231*t^11), {t, 0, 25}], t] (* _G. C. Greubel_, Apr 18 2016 *)` (wolfram-series)
* `%T coxG[{10, 231, -21}]` (wolfram-coxG)
* `%O (PARI) my(t='t+O('t^30)); Vec((1+t)*(1-t^10)/(1-22*t+252*t^10-231*t^11)) \\ _G. C. Greubel_, Sep 25 2019` (pari-vec)
* `%O (Magma) R<t>:=PowerSeriesRing(Integers(), 30); Coefficients(R!( (1+t)*(1-t^10)/(1-22*t+252*t^10-231*t^11) )); // _G. C. Greubel_, Sep 25 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A165939

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 25

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 25 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A165939 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 25).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 25 n h'
  have h2 : A165939 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A165939
