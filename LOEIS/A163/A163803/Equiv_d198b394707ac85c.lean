import LOEIS.A163.A163803.Defs

/-!
# A163803 — program transcriptions (`Equiv_d198b394707ac85c`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(1035*t^5 - 45*t^4 - 45*t^3 - 45*t^2 - 45*t + 1). a(n) = 45*a(n-1)+45*a(n-2)+45*a(n-3)+45*a(n-4)-1035*a(n-5). - _Wesley Ivan Hurt_, May 11 2021` (gf-rational)
* `%F a(n) = 45*a(n-1)+45*a(n-2)+45*a(n-3)+45*a(n-4)-1035*a(n-5). - _Wesley Ivan Hurt_, May 11 2021` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^5)/(1-46*t+1080*t^5-1035*t^6), {t, 0, 20}], t] (* _G. C. Greubel_, Aug 04 2017 *)` (wolfram-series)
* `%T coxG[{5, 1035, -45}]` (wolfram-coxG)
* `%O (PARI) my(t='t+O('t^20)); Vec((1+t)*(1-t^5)/(1-46*t+1080*t^5-1035*t^6)) \\ _G. C. Greubel_, Aug 04 2017` (pari-vec)
* `%O (Magma) R<t>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+t)*(1-t^5)/(1-46*t+1080*t^5-1035*t^6) )); // _G. C. Greubel_, Aug 09 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163803

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163803 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A163803 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163803
