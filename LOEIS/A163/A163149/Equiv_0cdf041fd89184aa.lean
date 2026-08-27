import LOEIS.A163.A163149.Defs

/-!
# A163149 — program transcriptions (`Equiv_0cdf041fd89184aa`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(210*t^4 - 20*t^3 - 20*t^2 - 20*t + 1). a(n) = -210*a(n-4) + 20*Sum_{k=1..3} a(n-k). - _Wesley Ivan Hurt_, May 05 2021` (gf-rational)
* `%F a(n) = -210*a(n-4) + 20*Sum_{k=1..3} a(n-k). - _Wesley Ivan Hurt_, May 05 2021` (recurrence)
* `%T CoefficientList[Series[(t^4 + 2 t^3 + 2 t^2 + 2 t + 1)/(210 t^4 - 20 t^3 - 20 t^2 - 20 t + 1), {t, 0, 16}], t] (* _Jinyuan Wang_, Mar 23 2020 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163149

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 16

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 16 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163149 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 16).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 16 n h'
  have h2 : A163149 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163149
