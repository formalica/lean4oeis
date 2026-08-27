import LOEIS.A163.A163923.Defs

/-!
# A163923 — program transcriptions (`Equiv_ac84c1ac95768bc6`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(15*t^6 - 5*t^5 - 5*t^4 - 5*t^3 - 5*t^2 - 5*t + 1). a(n) = 5*a(n-1)+5*a(n-2)+5*a(n-3)+5*a(n-4)+5*a(n-5)-15*a(n-6). - _Wesley Ivan Hurt_, Apr 23 2021` (gf-rational)
* `%F a(n) = 5*a(n-1)+5*a(n-2)+5*a(n-3)+5*a(n-4)+5*a(n-5)-15*a(n-6). - _Wesley Ivan Hurt_, Apr 23 2021` (recurrence)
* `%T coxG[{6,15,-5}]` (wolfram-coxG)
* `%T CoefficientList[Series[(1+t)*(1-t^6)/(1-6*t+20*t^6-15*t^7), {t,0,30}], t] (* _G. C. Greubel_, Aug 08 2017 *)` (wolfram-series)
* `%O (PARI) my(t='t+O('t^30)); Vec((1+t)*(1-t^6)/(1-6*t+20*t^6-15*t^7)) \\ _G. C. Greubel_, Aug 08 2017` (pari-vec)
* `%O (Magma) R<t>:=PowerSeriesRing(Integers(), 30); Coefficients(R!( (1+t)*(1-t^6)/(1-6*t+20*t^6-15*t^7) )); // _G. C. Greubel_, Aug 10 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163923

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163923 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A163923 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163923
