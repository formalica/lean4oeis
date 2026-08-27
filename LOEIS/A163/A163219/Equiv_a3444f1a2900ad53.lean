import LOEIS.A163.A163219.Defs

/-!
# A163219 — program transcriptions (`Equiv_a3444f1a2900ad53`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(595*t^4 - 34*t^3 - 34*t^2 - 34*t + 1). a(n) = -595*a(n-4) + 34*Sum_{k=1..3} a(n-k). - _Wesley Ivan Hurt_, May 05 2021` (gf-rational)
* `%F a(n) = -595*a(n-4) + 34*Sum_{k=1..3} a(n-k). - _Wesley Ivan Hurt_, May 05 2021` (recurrence)
* `%T CoefficientList[Series[(t^4+2*t^3+2*t^2+2*t+1)/(595*t^4-34*t^3-34*t^2 - 34*t+1), {t, 0, 20}], t] (* or *) Join[{1}, LinearRecurrence[{34, 34, 34, -595}, {36, 1260, 44100, 1542870}, 20]] (* _G. C. Greubel_, Dec 11 2016 *)` (wolfram-series)
* `%T coxG[{4, 595, -34}]` (wolfram-coxG)
* `%O (PARI) my(t='t+O('t^20)); Vec((t^4+2*t^3+2*t^2+2*t+1)/(595*t^4-34*t^3 - 34*t^2-34*t+1)) \\ _G. C. Greubel_, Dec 11 2016` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^4)/(1-35*x+629*x^4-595*x^5) )); // _G. C. Greubel_, Apr 30 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163219

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163219 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A163219 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163219
