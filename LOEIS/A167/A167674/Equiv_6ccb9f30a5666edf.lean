import LOEIS.A167.A167674.Defs

/-!
# A167674 — program transcriptions (`Equiv_6ccb9f30a5666edf`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(136*t^15 - 16*t^14 - 16*t^13 - 16*t^12 - 16*t^11 - 16*t^10 - 16*t^9 - 16*t^8 - 16*t^7 - 16*t^6 - 16*t^5 - 16*t^4 - 16*t^3 - 16*t^2 - 16*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(136*t^15 - 16*t^14 - 16*t^13 - 16*t^12 - 16*t^11 - 16*t^10 - 16*t^9 - 16*t^8 - 16*t^7 - 16*t^6 - 16*t^5 - 16*t^4 - 16*t^3 - 16*t^2 - 16*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Jun 19 2016 *)` (wolfram-series)
* `%O (PARI) first(n)=Vec((1+x^5+x^10)*(1+x+x^2+x^3+x^4)*(1+x)/(1-16*x-16*x^2-16*x^3-16*x^4-16*x^5-16*x^6-16*x^7-16*x^8-16*x^9-16*x^10-16*x^11-16*x^12-16*x^13-16*x^14+136*x^15)+O(x^(n+1))) \\ _Charles R Greathouse IV_, Jun 12 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167674

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167674 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167674 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167674
