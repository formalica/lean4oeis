import LOEIS.A167.A167049.Defs

/-!
# A167049 — program transcriptions (`Equiv_fd94512d179c60de`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(153*t^13 - 17*t^12 - 17*t^11 - 17*t^10 - 17*t^9 - 17*t^8 - 17*t^7 - 17*t^6 - 17*t^5 - 17*t^4 - 17*t^3 - 17*t^2 - 17*t + 1). G.f.: (1+x)*(1-x^13)/(1 - 18*x + 170*x^13 - 153*x^14). - _G. C. Greubel_, Apr 26 2019 a(n) = -153*a(n-13) + 17*Sum_{k=1..12} a(n-k). - _Wesley Ivan Hurt_, May 06 2021` (gf-rational)
* `%F G.f.: (t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(153*t^13 - 17*t^12 - 17*t^11 - 17*t^10 - 17*t^9 - 17*t^8 - 17*t^7 - 17*t^6 - 17*t^5 - 17*t^4 - 17*t^3 - 17*t^2 - 17*t + 1). G.f.: (1+x)*(1-x^13)/(1 - 18*x + 170*x^13 - 153*x^14). - _G. C. Greubel_, Apr 26 2019 a(n) = -153*a(n-13) + 17*Sum_{k=1..12} a(n-k). - _Wesley Ivan Hurt_, May 06 2021` (gf-factored)
* `%F a(n) = -153*a(n-13) + 17*Sum_{k=1..12} a(n-k). - _Wesley Ivan Hurt_, May 06 2021` (recurrence)
* `%T CoefficientList[Series[(1+x)*(1-x^13)/(1-18*x+170*x^13-153*x^14), {x, 0, 20}], x] (* _G. C. Greubel_, May 31 2016, modified Apr 26 2019 *)` (wolfram-series)
* `%T coxG[{13, 153, -17}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^13)/(1-18*x+170*x^13-153*x^14)) \\ _G. C. Greubel_, Apr 26 2019` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^13)/(1-18*x+170*x^13-153*x^14) )); // _G. C. Greubel_, Apr 26 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167049

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167049 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A167049 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167049
