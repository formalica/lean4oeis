import LOEIS.A162.A162755.Defs

/-!
# A162755 — program transcriptions (`Equiv_a15c8abf8c647af5`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^3 + 2*t^2 + 2*t + 1)/(28*t^3 - 7*t^2 - 7*t + 1) a(0)=1, a(1)=9, a(2)=72, a(3)=540, a(n)=7*a(n-1)+7*a(n-2)-28*a(n-3). - _Harvey P. Dale_, Jun 15 2011` (gf-rational)
* `%F a(0)=1, a(1)=9, a(2)=72, a(3)=540, a(n)=7*a(n-1)+7*a(n-2)-28*a(n-3). - _Harvey P. Dale_, Jun 15 2011` (recurrence)
* `%T CoefficientList[ Series[(t^3+2t^2+2t+1)/(28t^3-7t^2-7t+1),{t,0,50}],t] (* _Harvey P. Dale_, Jun 15 2011 *)` (wolfram-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A162755

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A162755 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A162755 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A162755
