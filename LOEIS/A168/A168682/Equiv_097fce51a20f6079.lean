import LOEIS.A168.A168682.Defs

/-!
# A168682 — program transcriptions (`Equiv_097fce51a20f6079`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1) / (6*t^17 - 3*t^16 - 3*t^15 - 3*t^14 - 3*t^13 - 3*t^12 - 3*t^11 - 3*t^10 - 3*t^9 - 3*t^8 - 3*t^7 - 3*t^6 - 3*t^5 - 3*t^4 - 3*t^3 - 3*t^2 - 3*t + 1). G.f.: (1+t)*(1-t^17)/(1 -4*t +9*t^17 -6*t^18). - _G. C. Greubel_, Feb 22 2021` (gf-rational)
* `%F G.f.: (t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1) / (6*t^17 - 3*t^16 - 3*t^15 - 3*t^14 - 3*t^13 - 3*t^12 - 3*t^11 - 3*t^10 - 3*t^9 - 3*t^8 - 3*t^7 - 3*t^6 - 3*t^5 - 3*t^4 - 3*t^3 - 3*t^2 - 3*t + 1). G.f.: (1+t)*(1-t^17)/(1 -4*t +9*t^17 -6*t^18). - _G. C. Greubel_, Feb 22 2021` (gf-factored)
* `%T CoefficientList[Series[(1+t)*(1-t^17)/(1 -4*t +9*t^17 -6*t^18), {t, 0, 40}], t] (* _G. C. Greubel_, Aug 03 2016, Feb 22 2021 *)` (wolfram-series)
* `%T coxG[{17, 6, -3, 40}]` (wolfram-coxG)
* `%O (PARI) Vec(Pol(vector(18,i,if(i<2||i>17,1,2))) / Pol(vector(18,i,if(i<2,6,i>17,1,-3)))+O(x^99)) \\ _Charles R Greathouse IV_, Aug 03 2016` (pari-vec)
* `%O R<t>:=PowerSeriesRing(Integers(), 40);` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168682

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 40

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 40 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168682 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 40).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 40 n h'
  have h2 : A168682 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168682
