import LOEIS.A163.A163226.Defs

/-!
# A163226 — program transcriptions (`Equiv_213118560eb0053a`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(861*t^4 - 41*t^3 - 41*t^2 - 41*t + 1). a(n) = 41*a(n-1)+41*a(n-2)+41*a(n-3)-861*a(n-4). - _Wesley Ivan Hurt_, May 06 2021` (gf-rational)
* `%F a(n) = 41*a(n-1)+41*a(n-2)+41*a(n-3)-861*a(n-4). - _Wesley Ivan Hurt_, May 06 2021` (recurrence)
* `%T CoefficientList[Series[(t^4+2*t^3+2*t^2+2*t+1)/(861*t^4-41*t^3-41*t^2 - 41*t+1), {t,0,20}], t] (* or *) Join[{1}, LinearRecurrence[ {41, 41, 41, -861}, {43,1806,75852,3184881}, 20]] (* _G. C. Greubel_, Dec 11 2016 *)` (wolfram-series)
* `%O (PARI) my(t='t+O('t^20)); Vec((t^4+2*t^3+2*t^2+2*t+1)/(861*t^4-41*t^3 - 41*t^2-41*t+1)) \\ _G. C. Greubel_, Dec 11 2016` (pari-vec)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 20); Coefficients(R!( (1+x)*(1-x^4)/(1-42*x+902*x^4-861*x^5) )); // _G. C. Greubel_, Apr 30 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163226

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163226 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A163226 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163226
