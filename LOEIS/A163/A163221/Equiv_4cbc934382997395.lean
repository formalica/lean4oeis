import LOEIS.A163.A163221.Defs

/-!
# A163221 — program transcriptions (`Equiv_4cbc934382997395`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(666*t^4 - 36*t^3 - 36*t^2 - 36*t + 1). a(n) = 36*a(n-1)+36*a(n-2)+36*a(n-3)-666*a(n-4). - _Wesley Ivan Hurt_, May 06 2021` (gf-rational)
* `%F a(n) = 36*a(n-1)+36*a(n-2)+36*a(n-3)-666*a(n-4). - _Wesley Ivan Hurt_, May 06 2021` (recurrence)
* `%T coxG[{4,666,-36}]` (wolfram-coxG)
* `%T CoefficientList[Series[(t^4+2*t^3+2*t^2+2*t+1)/(666*t^4-36*t^3-36*t^2 - 36*t+1), {t,0,20}], t] (* or *) LinearRecurrence[{36, 36, 36, -666}, {1, 38, 1406, 52022, 1924111}, 20] (* _G. C. Greubel_, Dec 11 2016; modified by _Georg Fischer_, Apr 08 2019 *)` (wolfram-series)
* `%O (PARI) my(t='t+O('t^20)); Vec((t^4+2*t^3+2*t^2+2*t+1)/(666*t^4-36*t^3 - 36*t^2-36*t+1)) \\ _G. C. Greubel_, Dec 11 2016` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^4)/(1-37*x+702*x^4-666*x^5) )); // _G. C. Greubel_, May 01 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163221

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163221 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A163221 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163221
