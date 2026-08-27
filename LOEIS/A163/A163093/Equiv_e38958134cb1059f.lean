import LOEIS.A163.A163093.Defs

/-!
# A163093 — program transcriptions (`Equiv_e38958134cb1059f`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(120*t^4 - 15*t^3 - 15*t^2 - 15*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^4 + 2 t^3 + 2 t^2 + 2 t + 1)/(120 t^4 - 15 t^3 - 15 t^2 - 15 t + 1), {t, 0, 20}], t] (* _Jinyuan Wang_, Mar 23 2020 *)` (wolfram-series)
* `%T coxG[{4,120,-15}]` (wolfram-coxG)
* `%O (PARI) a(n)=if(n,([0,1,0,0; 0,0,1,0; 0,0,0,1; -120,15,15,15]^(n-1)*[17;272;4352;69496])[1,1],1) \\ _Charles R Greathouse IV_, Aug 14 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A163093

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 20

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 20 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A163093 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 20).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 20 n h'
  have h2 : A163093 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A163093
