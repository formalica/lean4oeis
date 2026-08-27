import LOEIS.A164.A164610.Defs

/-!
# A164610 — program transcriptions (`Equiv_9af0aa035bf6905f`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(66*t^7 - 11*t^6 - 11*t^5 - 11*t^4 - 11*t^3 - 11*t^2 - 11*t + 1). a(n) = -66*a(n-7) + 11*Sum_{k=1..6} a(n-k). - _Wesley Ivan Hurt_, May 11 2021` (gf-rational)
* `%F a(n) = -66*a(n-7) + 11*Sum_{k=1..6} a(n-k). - _Wesley Ivan Hurt_, May 11 2021` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^7)/(1-12*t+77*t^7-66*t^8), {t, 0, 20}], t] (* _G. C. Greubel_, Aug 10 2017 *)` (wolfram-series)
* `%O (PARI) my(t='t+O('t^20)); Vec((1+t)*(1-t^7)/(1-12*t+77*t^7-66*t^8)) \\ _G. C. Greubel_, Aug 10 2017` (pari-vec)
* `%O (Magma) R<t>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+t)*(1-t^7)/(1-12*t+77*t^7-66*t^8) )); // _G. C. Greubel_, Sep 15 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A164610

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A164610 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A164610 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A164610
