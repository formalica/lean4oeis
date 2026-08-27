import LOEIS.A163.A163924.Defs

/-!
# A163924 — program transcriptions (`Equiv_842e692a77d9328a`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(21*t^6 - 6*t^5 - 6*t^4 - 6*t^3 - 6*t^2 - 6*t + 1). a(n) = -21*a(n-6) + 6*Sum_{k=1..5} a(n-k). - _Wesley Ivan Hurt_, May 11 2021` (gf-rational)
* `%F a(n) = -21*a(n-6) + 6*Sum_{k=1..5} a(n-k). - _Wesley Ivan Hurt_, May 11 2021` (recurrence)
* `%T coxG[{6,21,-6}]` (wolfram-coxG)
* `%T CoefficientList[Series[(1+t)*(1-t^6)/(1-7*t+27*t^6-21*t^7), {t,0,30}], t] (* _G. C. Greubel_, Aug 08 2017 *)` (wolfram-series)
* `%O (PARI) my(t='t+O('t^30)); Vec((1+t)*(1-t^6)/(1-7*t+27*t^6-21*t^7)) \\ _G. C. Greubel_, Aug 08 2017` (pari-vec)
* `%O (Magma) R<t>:=PowerSeriesRing(Integers(), 30); Coefficients(R!( (1+t)*(1-t^6)/(1-7*t+27*t^6-21*t^7) )); // _G. C. Greubel_, Aug 10 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163924

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163924 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A163924 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163924
