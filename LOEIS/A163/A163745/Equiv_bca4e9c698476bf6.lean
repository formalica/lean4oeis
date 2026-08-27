import LOEIS.A163.A163745.Defs

/-!
# A163745 — program transcriptions (`Equiv_bca4e9c698476bf6`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(861*t^5 - 41*t^4 - 41*t^3 - 41*t^2 - 41*t + 1). a(n) = 41*a(n-1)+41*a(n-2)+41*a(n-3)+41*a(n-4)-861*a(n-5). - _Wesley Ivan Hurt_, May 11 2021` (gf-rational)
* `%F a(n) = 41*a(n-1)+41*a(n-2)+41*a(n-3)+41*a(n-4)-861*a(n-5). - _Wesley Ivan Hurt_, May 11 2021` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^5)/(1-42*t+902*t^5-861*t^6), {t, 0, 20}], t] (* _G. C. Greubel_, Aug 02 2017 *)` (wolfram-series)
* `%O (PARI) my(t='t+O('t^20)); Vec((1+t)*(1-t^5)/(1-42*t+902*t^5-861*t^6)) \\ _G. C. Greubel_, Aug 02 2017` (pari-vec)
* `%O (Magma) R<t>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+t)*(1-t^5)/(1-42*t+902*t^5-861*t^6) )); // _G. C. Greubel_, Aug 09 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163745

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163745 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A163745 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163745
