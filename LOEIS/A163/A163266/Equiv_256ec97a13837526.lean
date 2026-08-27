import LOEIS.A163.A163266.Defs

/-!
# A163266 — program transcriptions (`Equiv_256ec97a13837526`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(1081*t^4 - 46*t^3 - 46*t^2 - 46*t + 1). a(n) = 46*a(n-1)+46*a(n-2)+46*a(n-3)-1081*a(n-4). - _Wesley Ivan Hurt_, May 10 2021` (gf-rational)
* `%F a(n) = 46*a(n-1)+46*a(n-2)+46*a(n-3)-1081*a(n-4). - _Wesley Ivan Hurt_, May 10 2021` (recurrence)
* `%T CoefficientList[Series[(t^4+2*t^3+2*t^2+2*t+1)/(1081*t^4-46*t^3-46*t^2 - 46*t+1), {t,0,20}], t] (* or *) LinearRecurrence[ {46,46,46,-1081}, {1,48,2256,106032,4982376}, 20] (* _G. C. Greubel_, Dec 12 2016 *)` (wolfram-series)
* `%T coxG[{4, 1081, -46}]` (wolfram-coxG)
* `%O (PARI) my(t='t+O('t^20)); Vec((t^4+2*t^3+2*t^2+2*t+1)/(1081*t^4-46*t^3 - 46*t^2-46*t+1)) \\ _G. C. Greubel_, Dec 12 2016` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^4)/(1-47*x+1127*x^4-1081*x^5) )); // _G. C. Greubel_, May 01 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163266

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163266 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A163266 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163266
