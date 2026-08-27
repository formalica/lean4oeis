import LOEIS.A163.A163218.Defs

/-!
# A163218 — program transcriptions (`Equiv_62b47959ba1e3156`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(561*t^4 - 33*t^3 - 33*t^2 - 33*t + 1). a(n) = -561*a(n-4) + 33*Sum_{k=1..3} a(n-k). - _Wesley Ivan Hurt_, May 05 2021` (gf-rational)
* `%F a(n) = -561*a(n-4) + 33*Sum_{k=1..3} a(n-k). - _Wesley Ivan Hurt_, May 05 2021` (recurrence)
* `%T CoefficientList[Series[(t^4+2*t^3+2*t^2+2*t+1)/(561*t^4-33*t^3-33*t^2 - 33*t+1), {t,0,20}], t] (* or *) LinearRecurrence[{33, 33, 33, -561}, {1, 35, 1190, 40460}, 20] (* _G. C. Greubel_, Dec 11 2016 *)` (wolfram-series)
* `%T coxG[{4, 561, -33}]` (wolfram-coxG)
* `%O (PARI) my(t='t+O('t^20)); Vec((t^4+2*t^3+2*t^2+2*t+1)/(561*t^4-33*t^3 - 33*t^2-33*t+1)) \\ _G. C. Greubel_, Dec 11 2016` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^4)/(1-34*x+594*x^4-x^561*x^5) )); // _G. C. Greubel_, Apr 30 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163218

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163218 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A163218 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163218
