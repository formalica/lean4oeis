import LOEIS.A163.A163749.Defs

/-!
# A163749 — program transcriptions (`Equiv_8508ffa8d966855d`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(946*t^5 - 43*t^4 - 43*t^3 - 43*t^2 - 43*t + 1). a(n) = 43*a(n-1)+43*a(n-2)+43*a(n-3)+43*a(n-4)-946*a(n-5). - _Wesley Ivan Hurt_, May 11 2021` (gf-rational)
* `%F a(n) = 43*a(n-1)+43*a(n-2)+43*a(n-3)+43*a(n-4)-946*a(n-5). - _Wesley Ivan Hurt_, May 11 2021` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^5)/(1-44*t+989*t^5-946*t^6), {t, 0, 20}], t] (* _G. C. Greubel_, Aug 02 2017 *)` (wolfram-series)
* `%T coxG[{5, 946, -43}]` (wolfram-coxG)
* `%O (PARI) my(t='t+O('t^20)); Vec((1+t)*(1-t^5)/(1-44*t+989*t^5-946*t^6)) \\ _G. C. Greubel_, Aug 02 2017` (pari-vec)
* `%O (Magma) R<t>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+t)*(1-t^5)/(1-43*t+945*t^5-903*t^6) )); // _G. C. Greubel_, Aug 09 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163749

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163749 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A163749 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163749
