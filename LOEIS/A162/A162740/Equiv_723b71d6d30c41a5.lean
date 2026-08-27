import LOEIS.A162.A162740.Defs

/-!
# A162740 — program transcriptions (`Equiv_723b71d6d30c41a5`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (x^3 + 2*x^2 + 2*x + 1)/(3*x^3 - 2*x^2 - 2*x + 1). From _Bruno Berselli_, Dec 28 2015: (Start) a(n) = 2*a(n-1) + 2*a(n-2) - 3*a(n-3) for n>3. a(n) = -2 + ((-7+2*sqrt(13))*(1-sqrt(13))^n + (7+2*sqrt(13))*(1+sqrt(13))^n)/(3*sqrt(13)*2^(n-1)) for n>0. (End) G.f.: (1+x)*(1-x^3)/(1 -3*x +5*x^3 -3*x^4). - _G. C. Greubel_, Apr 25 2019` (gf-rational)
* `%F G.f.: (x^3 + 2*x^2 + 2*x + 1)/(3*x^3 - 2*x^2 - 2*x + 1). From _Bruno Berselli_, Dec 28 2015: (Start) a(n) = 2*a(n-1) + 2*a(n-2) - 3*a(n-3) for n>3. a(n) = -2 + ((-7+2*sqrt(13))*(1-sqrt(13))^n + (7+2*sqrt(13))*(1+sqrt(13))^n)/(3*sqrt(13)*2^(n-1)) for n>0. (End) G.f.: (1+x)*(1-x^3)/(1 -3*x +5*x^3 -3*x^4). - _G. C. Greubel_, Apr 25 2019` (gf-factored)
* `%F a(n) = 2*a(n-1) + 2*a(n-2) - 3*a(n-3) for n>3.` (recurrence)
* `%T CoefficientList[Series[(x^3+2x^2+2x+1)/(3x^3-2x^2-2x+1), {x, 0, 40}], x ] (* _Vincenzo Librandi_, Apr 29 2014 *)` (wolfram-series)
* `%T coxG[{3, 3, -2, 40}]` (wolfram-coxG)
* `%O (Magma) m:=40; R<x>:=PowerSeriesRing(Integers(), m); b:=func<k|(1-x^k)/(1-x)>; Coefficients(R!(b(2)*b(3)/(1-2*x-2*x^2+3*x^3))); // _Bruno Berselli_, Dec 28 2015 - see Chapovalov et al.` (magma-series)
* `%O (PARI) my(x='x+O('x^40)); Vec((1+x)*(1-x^3)/(1-3*x+5*x^3-3*x^4)) \\ _G. C. Greubel_, Apr 25 2019` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A162740

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 40

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 40 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A162740 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 40).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 40 n h'
  have h2 : A162740 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A162740
