import LOEIS.A164.A164351.Defs

/-!
# A164351 — program transcriptions (`Equiv_3934b212a03f87c6`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(1176*t^6 - 48*t^5 - 48*t^4 - 48*t^3 - 48*t^2 - 48*t + 1). a(n) = -1176*a(n-6) + 48*Sum_{k=1..5} a(n-k). - _Wesley Ivan Hurt_, May 11 2021` (gf-rational)
* `%F a(n) = -1176*a(n-6) + 48*Sum_{k=1..5} a(n-k). - _Wesley Ivan Hurt_, May 11 2021` (recurrence)
* `%T coxG[{6,1176,-48}]` (wolfram-coxG)
* `%T CoefficientList[Series[(1+t)*(1-t^6)/(1-49*t+1224*t^6-1176*t^7), {t, 0, 20}], t] (* _G. C. Greubel_, Sep 15 2017 *)` (wolfram-series)
* `%O (PARI) my(t='t+O('t^20)); Vec((1+t)*(1-t^6)/(1-49*t+1224*t^6-1176*t^7)) \\ _G. C. Greubel_, Sep 15 2017` (pari-vec)
* `%O (Magma) R<t>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+t)*(1-t^6)/(1-49*t+1224*t^6-1176*t^7) )); // _G. C. Greubel_, Aug 24 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A164351

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A164351 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A164351 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A164351
