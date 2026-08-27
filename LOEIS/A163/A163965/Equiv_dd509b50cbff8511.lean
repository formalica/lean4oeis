import LOEIS.A163.A163965.Defs

/-!
# A163965 — program transcriptions (`Equiv_dd509b50cbff8511`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(120*t^6 - 15*t^5 - 15*t^4 - 15*t^3 - 15*t^2 - 15*t + 1). a(n) = -120*a(n-6) + 15*Sum_{k=1..5} a(n-k). - _Wesley Ivan Hurt_, May 11 2021` (gf-rational)
* `%F a(n) = -120*a(n-6) + 15*Sum_{k=1..5} a(n-k). - _Wesley Ivan Hurt_, May 11 2021` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^6)/(1-16*t+135*t^6-120*t^7), {t,0,30}], t] (* _G. C. Greubel_, Aug 23 2017 *)` (wolfram-series)
* `%T coxG[{6, 120, -15}]` (wolfram-coxG)
* `%O (PARI) my(t='t+O('t^30)); Vec((1+t)*(1-t^6)/(1-16*t+135*t^6-120*t^7)) \\ _G. C. Greubel_, Aug 23 2017` (pari-vec)
* `%O (Magma) R<t>:=PowerSeriesRing(Integers(), 30); Coefficients(R!( (1+t)*(1-t^6)/(1-16*t+135*t^6-120*t^7) )); // _G. C. Greubel_, Aug 11 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163965

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163965 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A163965 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163965
