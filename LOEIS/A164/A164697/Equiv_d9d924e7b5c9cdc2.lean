import LOEIS.A164.A164697.Defs

/-!
# A164697 — program transcriptions (`Equiv_d9d924e7b5c9cdc2`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (x^8 + 2*x^7 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 2*x + 1)/( 3*x^8 - 2*x^7 - 2*x^6 - 2*x^5 - 2*x^4 - 2*x^3 - 2*x^2 - 2*x + 1). a(n) = -3*a(n-8) + 2*Sum_{k=1..7} a(n-k). - _Wesley Ivan Hurt_, May 11 2021` (gf-rational)
* `%F a(n) = -3*a(n-8) + 2*Sum_{k=1..7} a(n-k). - _Wesley Ivan Hurt_, May 11 2021` (recurrence)
* `%T CoefficientList[Series[(x^8 +2x^7 +2x^6 +2x^5 +2x^4 +2x^3 +2x^2 +2x +1)/( 3x^8 -2x^7 -2x^6 -2x^5 -2x^4 -2x^3 -2x^2 -2x +1), {x, 0, 40}], x ] (* _Vincenzo Librandi_, Apr 29 2014 *)` (wolfram-series)
* `%T coxG[{8,3,-2,30}]` (wolfram-coxG)
* `%O (PARI) my(t='t+O('t^30)); Vec((1+t)*(1-t^8)/(1-3*t+5*t^8-3*t^9)) \\ _G. C. Greubel_, Sep 16 2019` (pari-vec)
* `%O (Magma) R<t>:=PowerSeriesRing(Integers(), 30); Coefficients(R!( (1+t)*(1-t^8)/(1-3*t+5*t^8-3*t^9) )); // _G. C. Greubel_, Sep 16 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A164697

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 40

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 40 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A164697 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 40).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 40 n h'
  have h2 : A164697 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A164697
