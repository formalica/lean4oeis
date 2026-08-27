import LOEIS.A163.A163222.Defs

/-!
# A163222 — program transcriptions (`Equiv_2cd0877544eb49a6`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(703*t^4 - 37*t^3 - 37*t^2 - 37*t + 1). a(n) = 37*a(n-1)+37*a(n-2)+37*a(n-3)-703*a(n-4). - _Wesley Ivan Hurt_, May 06 2021` (gf-rational)
* `%F a(n) = 37*a(n-1)+37*a(n-2)+37*a(n-3)-703*a(n-4). - _Wesley Ivan Hurt_, May 06 2021` (recurrence)
* `%T CoefficientList[Series[(t^4+2*t^3+2*t^2+2*t+1)/(703*t^4-37*t^3-37*t^2 - 37*t+1), {t,0,20}], t] (* or *) Join[{1}, LinearRecurrence[{37, 37, 37, -703}, {39, 1482, 56316, 2139267}, 20]] (* _G. C. Greubel_, Dec 11 2016 *)` (wolfram-series)
* `%T coxG[{4, 703, -37}]` (wolfram-coxG)
* `%O (PARI) my(t='t+O('t^20)); Vec((t^4+2*t^3+2*t^2+2*t+1)/(703*t^4-37*t^3 - 37*t^2-37*t+1)) \\ _G. c. Greubel_, Dec 11 2016` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^4)/(1-38*x+740*x^4-703*x^5) )); // _G. C. Greubel_, Apr 30 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163222

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163222 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A163222 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163222
