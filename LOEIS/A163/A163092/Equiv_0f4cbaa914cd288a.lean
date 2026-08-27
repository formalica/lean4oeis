import LOEIS.A163.A163092.Defs

/-!
# A163092 — program transcriptions (`Equiv_0f4cbaa914cd288a`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(105*t^4 - 14*t^3 - 14*t^2 - 14*t + 1).` (gf-rational)
* `%T CoefficientList[ Series[(t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(105*t^4 - 14*t^3 - 14*t^2 - 14*t + 1), {t, 0, 16}], t] (* _Jean-François Alcover_, Nov 26 2013 *)` (wolfram-series)
* `%O (PARI) Vec((t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(105*t^4 - 14*t^3 - 14*t^2 - 14*t + 1) + O(t^20)) \\ _Jinyuan Wang_, Mar 23 2020` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163092

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 16

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 16 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163092 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 16).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 16 n h'
  have h2 : A163092 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163092
