import LOEIS.A163.A163265.Defs

/-!
# A163265 — program transcriptions (`Equiv_ad52bd44fcf804fa`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(1035*t^4 - 45*t^3 - 45*t^2 - 45*t + 1). a(n) = 45*a(n-1)+45*a(n-2)+45*a(n-3)-1035*a(n-4). - _Wesley Ivan Hurt_, May 10 2021` (gf-rational)
* `%F a(n) = 45*a(n-1)+45*a(n-2)+45*a(n-3)-1035*a(n-4). - _Wesley Ivan Hurt_, May 10 2021` (recurrence)
* `%T CoefficientList[Series[(t^4+2*t^3+2*t^2+2*t+1)/(1035*t^4-45*t^3-45*t^2 - 45*t+1), {t,0,20}], t] (* or *) LinearRecurrence[ {45, 45, 45, -1035}, {1,47,2162,99452,4573711}, 20] (* _G. C. Greubel_, Dec 12 2016 *)` (wolfram-series)
* `%T coxG[{4, 1035, -45}]` (wolfram-coxG)
* `%O (PARI) my(t='t+O('t^20)); Vec((t^4+2*t^3+2*t^2+2*t+1)/(1035*t^4-45*t^3- 45*t^2-45*t+1)) \\ _G. C. Greubel_, Dec 12 2016` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^4)/(1-46*x+1080*x^4-1035*x^5) )); // _G. C. Greubel_, May 01 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163265

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163265 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A163265 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163265
