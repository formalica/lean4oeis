import LOEIS.A163.A163878.Defs

/-!
# A163878 — program transcriptions (`Equiv_515cdeb25ed9c777`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(6*t^6 - 3*t^5 - 3*t^4 - 3*t^3 - 3*t^2 - 3*t + 1). a(n) = -6*a(n-6) + 3*Sum_{k=1..5} a(n-k). - _Wesley Ivan Hurt_, May 11 2021` (gf-rational)
* `%F a(n) = -6*a(n-6) + 3*Sum_{k=1..5} a(n-k). - _Wesley Ivan Hurt_, May 11 2021` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^6)/(1-4*t+9*t^6-6*t^7), {t, 0, 30}], t] (* _G. C. Greubel_, Aug 07 2017 *)` (wolfram-series)
* `%T coxG[{6, 6, -3}]` (wolfram-coxG)
* `%O (PARI) my(t='t+O('t^30)); Vec((1+t)*(1-t^6)/(1-4*t+9*t^6-6*t^7)) \\ _G. C. Greubel_, Aug 07 2017` (pari-vec)
* `%O (Magma) R<t>:=PowerSeriesRing(Integers(), 30); Coefficients(R!( (1+t)*(1-t^6)/(1-4*t+9*t^6-6*t^7) )); // _G. C. Greubel_, Aug 10 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163878

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 30

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 30 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163878 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 30).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 30 n h'
  have h2 : A163878 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163878
