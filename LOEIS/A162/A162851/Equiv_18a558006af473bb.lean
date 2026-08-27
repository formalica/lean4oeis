import LOEIS.A162.A162851.Defs

/-!
# A162851 — program transcriptions (`Equiv_18a558006af473bb`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^3 + 2*t^2 + 2*t + 1)/(630*t^3 - 35*t^2 - 35*t + 1). G.f.: (1+x)*(1-x^3)/(1 - 36*x + 665*x^3 - 630*x^4). - _G. C. Greubel_, Apr 26 2019 a(n) = 35*a(n-1)+35*a(n-2)-630*a(n-3). - _Wesley Ivan Hurt_, May 05 2021` (gf-rational)
* `%F G.f.: (t^3 + 2*t^2 + 2*t + 1)/(630*t^3 - 35*t^2 - 35*t + 1). G.f.: (1+x)*(1-x^3)/(1 - 36*x + 665*x^3 - 630*x^4). - _G. C. Greubel_, Apr 26 2019 a(n) = 35*a(n-1)+35*a(n-2)-630*a(n-3). - _Wesley Ivan Hurt_, May 05 2021` (gf-factored)
* `%F a(n) = 35*a(n-1)+35*a(n-2)-630*a(n-3). - _Wesley Ivan Hurt_, May 05 2021` (recurrence)
* `%T CoefficientList[Series[(t^3+2*t^2+2*t+1)/(630*t^3-35*t^2-35*t+1), {t, 0, 20}], t] (* or *) LinearRecurrence[{35, 35, -630}, {1, 37, 1332}, 20] (* _G. C. Greubel_, Oct 24 2018 *)` (wolfram-series)
* `%T coxG[{3, 630, -35}]` (wolfram-coxG)
* `%O (PARI) my(t='t+O('t^20)); Vec((t^3+2*t^2+2*t+1)/(630*t^3-35*t^2-35*t+1)) \\ _G. C. Greubel_, Oct 24 2018` (pari-vec)
* `%O (Magma) R<t>:=PowerSeriesRing(Integers(), 20); Coefficients(R!((t^3 +2*t^2+2*t+1)/(630*t^3-35*t^2-35*t+1))); // _G. C. Greubel_, Oct 24 2018` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A162851

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A162851 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A162851 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A162851
