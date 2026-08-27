import LOEIS.A164.A164352.Defs

/-!
# A164352 — program transcriptions (`Equiv_224a0503950e8fdb`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F a(n) = 2*a(n-1)-a(n-2)+2*a(n-3)-a(n-4)+2*a(n-5)-a(n-6). - _Wesley Ivan Hurt_, May 11 2021` (recurrence)
* `%T CoefficientList[Series[(1-t^7)/((1-t)*(1-2*t+t^2-2*t^3+t^4-2*t^5+t^6)), {t,0,35}], t] (* _G. C. Greubel_, Sep 15 2017 *)` (wolfram-series)
* `%O (PARI) (t='t+O('t^35)); Vec((1-t^7)/((1-t)*(1-2*t+t^2-2*t^3+t^4-2*t^5 +t^6))) \\ _G. C. Greubel_, Sep 15 2017` (pari-vec)
* `%O (Magma) R<t>:=PowerSeriesRing(Integers(), 35); Coefficients(R!( (1-t^7)/( (1-t)*(1-2*t+t^2-2*t^3+t^4-2*t^5+t^6)) )); // _G. C. Greubel_, Aug 24 2019` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A164352

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A164352 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A164352 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A164352
