import LOEIS.A164.A164353.Defs

/-!
# A164353 — program transcriptions (`Equiv_4f56a646f6b778b8`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (x^7 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 2*x + 1)/(3*x^7 - 2*x^6 - 2*x^5 - 2*x^4 - 2*x^3 - 2*x^2 - 2*x + 1). a(n) = -3*a(n-7) + 2*Sum_{k=1..6} a(n-k). - _Wesley Ivan Hurt_, May 11 2021` (gf-rational)
* `%F a(n) = -3*a(n-7) + 2*Sum_{k=1..6} a(n-k). - _Wesley Ivan Hurt_, May 11 2021` (recurrence)
* `%T CoefficientList[Series[(x^7 + 2 x^6 + 2 x^5 + 2 x^4 + 2 x^3 + 2 x^2 + 2 x + 1)/(3 x^7 - 2 x^6 - 2 x^5 - 2 x^4 - 2 x^3 - 2 x^2 - 2 x + 1), {x, 0, 40}], x ] (* _Vincenzo Librandi_, Apr 29 2014 *)` (wolfram-series)
* `%T coxG[{7,3,-2,30}]` (wolfram-coxG)
* `%O (PARI) my(t='t+O('t^30)); Vec((1+t)*(1-t^7)/(1-3*t+5*t^7-3*t^8)) \\ _G. C. Greubel_, Sep 15 2017` (pari-vec)
* `%O (Magma) R<t>:=PowerSeriesRing(Integers(), 30); Coefficients(R!( (1+t)*(1-t^7)/(1-3*t+5*t^7-3*t^8) )); // _G. C. Greubel_, Aug 24 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A164353

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 40

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 40 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A164353 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 40).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 40 n h'
  have h2 : A164353 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A164353
