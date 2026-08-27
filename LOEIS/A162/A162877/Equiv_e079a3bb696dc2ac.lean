import LOEIS.A162.A162877.Defs

/-!
# A162877 — program transcriptions (`Equiv_e079a3bb696dc2ac`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^3 + 2*t^2 + 2*t + 1)/(741*t^3 - 38*t^2 - 38*t + 1). a(n) = 38*a(n-1) + 38*a(n-2) - 741*a(n-3), n > 0. - _Muniru A Asiru_, Oct 24 2018 G.f.: (1+x)*(1-x^3)/(1 - 39*x + 779*x^3 - 741*x^4). - _G. C. Greubel_, Apr 27 2019` (gf-rational)
* `%F G.f.: (t^3 + 2*t^2 + 2*t + 1)/(741*t^3 - 38*t^2 - 38*t + 1). a(n) = 38*a(n-1) + 38*a(n-2) - 741*a(n-3), n > 0. - _Muniru A Asiru_, Oct 24 2018 G.f.: (1+x)*(1-x^3)/(1 - 39*x + 779*x^3 - 741*x^4). - _G. C. Greubel_, Apr 27 2019` (gf-factored)
* `%F a(n) = 38*a(n-1) + 38*a(n-2) - 741*a(n-3), n > 0. - _Muniru A Asiru_, Oct 24 2018` (recurrence)
* `%T coxG[{3,741,-38}]` (wolfram-coxG)
* `%T CoefficientList[Series[(t^3+2*t^2+2*t+1)/(741*t^3-38*t^2-38*t+1), {t, 0, 20}], t] (* _G. C. Greubel_, Oct 24 2018 *)` (wolfram-series)
* `%O (PARI) my(t='t+O('t^20)); Vec((t^3+2*t^2+2*t+1)/(741*t^3-38*t^2-38*t+1)) \\ _G. C. Greubel_, Oct 24 2018` (pari-vec)
* `%O (Magma) R<t>:=PowerSeriesRing(Integers(), 20); Coefficients(R!((t^3 + 2*t^2+2*t+1)/(741*t^3-38*t^2-38*t+1))); // _G. C. Greubel_, Oct 24 2018` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A162877

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A162877 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A162877 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A162877
