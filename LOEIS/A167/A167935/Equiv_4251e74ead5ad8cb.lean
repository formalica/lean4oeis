import LOEIS.A167.A167935.Defs

/-!
# A167935 — program transcriptions (`Equiv_4251e74ead5ad8cb`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(210*t^16 - 20*t^15 - 20*t^14 - 20*t^13 - 20*t^12 - 20*t^11 - 20*t^10 - 20*t^9 - 20*t^8 - 20*t^7 - 20*t^6 - 20*t^5 - 20*t^4 - 20*t^3 - 20*t^2 - 20*t + 1). G.f.: (1+x)*(1-x^16)/(1 - 21*x + 230*x^16 - 210*x^17). - _G. C. Greubel_, Apr 26 2019 a(n) = -210*a(n-16) + 20*Sum_{k=1..15} a(n-k). - _Wesley Ivan Hurt_, May 06 2021` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(210*t^16 - 20*t^15 - 20*t^14 - 20*t^13 - 20*t^12 - 20*t^11 - 20*t^10 - 20*t^9 - 20*t^8 - 20*t^7 - 20*t^6 - 20*t^5 - 20*t^4 - 20*t^3 - 20*t^2 - 20*t + 1). G.f.: (1+x)*(1-x^16)/(1 - 21*x + 230*x^16 - 210*x^17). - _G. C. Greubel_, Apr 26 2019 a(n) = -210*a(n-16) + 20*Sum_{k=1..15} a(n-k). - _Wesley Ivan Hurt_, May 06 2021` (gf-factored)
* `%F a(n) = -210*a(n-16) + 20*Sum_{k=1..15} a(n-k). - _Wesley Ivan Hurt_, May 06 2021` (recurrence)
* `%T CoefficientList[Series[(1+x)*(1-x^16)/(1-21*x+230*x^16-210*x^17), {x, 0, 20}], x] (* _G. C. Greubel_, Jul 01 2016, modified Apr 26 2019 *)` (wolfram-series)
* `%T coxG[{16, 210, -20}]` (wolfram-coxG)
* `%O (PARI) my(x='x+O('x^20)); Vec((1+x)*(1-x^16)/(1-21*x+230*x^16-210*x^17)) \\ _G. C. Greubel_, Apr 26 2019` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^16)/(1-21*x+230*x^16-210*x^17) )); // _G. C. Greubel_, Apr 26 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167935

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167935 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A167935 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167935
