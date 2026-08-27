import LOEIS.A168.A168881.Defs

/-!
# A168881 — program transcriptions (`Equiv_513da9a37c54367d`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(55*t^21 - 10*t^20 - 10*t^19 - 10*t^18 - 10*t^17 - 10*t^16 - 10*t^15 - 10*t^14 - 10*t^13 - 10*t^12 - 10*t^11 - 10*t^10 - 10*t^9 - 10*t^8 - 10*t^7 - 10*t^6 - 10*t^5 - 10*t^4 - 10*t^3 - 10*t^2 - 10*t + 1). G.f.: (1+t)*(1-t^21)/(1 -11*t +65*t^21 -55*t^22). - _G. C. Greubel_, Sep 25 2019` (gf-rational)
* `%F G.f.: (t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(55*t^21 - 10*t^20 - 10*t^19 - 10*t^18 - 10*t^17 - 10*t^16 - 10*t^15 - 10*t^14 - 10*t^13 - 10*t^12 - 10*t^11 - 10*t^10 - 10*t^9 - 10*t^8 - 10*t^7 - 10*t^6 - 10*t^5 - 10*t^4 - 10*t^3 - 10*t^2 - 10*t + 1). G.f.: (1+t)*(1-t^21)/(1 -11*t +65*t^21 -55*t^22). - _G. C. Greubel_, Sep 25 2019` (gf-factored)
* `%T CoefficientList[Series[(1+t)*(1-t^21)/(1-11*t+65*t^21-55*t^22), {t, 0, 20}], t] (* _G. C. Greubel_, Sep 25 2019 *)` (wolfram-series)
* `%T coxG[{21, 55, -10}]` (wolfram-coxG)
* `%O (PARI) my(t='t+O('t^20)); Vec((1+t)*(1-t^21)/(1-11*t+65*t^21-55*t^22)) \\ _G. C. Greubel_, Sep 25 2019` (pari-vec)
* `%O (Magma) R<t>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+t)*(1-t^21)/(1-11*t+65*t^21-55*t^22) )); // _G. C. Greubel_, Sep 25 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168881

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168881 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A168881 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168881
