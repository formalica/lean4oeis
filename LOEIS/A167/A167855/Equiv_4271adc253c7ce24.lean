import LOEIS.A167.A167855.Defs

/-!
# A167855 — program transcriptions (`Equiv_4271adc253c7ce24`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(946*t^15 - 43*t^14 - 43*t^13 - 43*t^12 - 43*t^11 - 43*t^10 - 43*t^9 - 43*t^8 - 43*t^7 - 43*t^6 - 43*t^5 - 43*t^4 - 43*t^3 - 43*t^2 - 43*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(946*t^15 - 43*t^14 - 43*t^13 - 43*t^12 - 43*t^11 - 43*t^10 - 43*t^9 - 43*t^8 - 43*t^7 - 43*t^6 - 43*t^5 - 43*t^4 - 43*t^3 - 43*t^2 - 43*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Jun 28 2016 *)` (wolfram-series)
* `%O (PARI) first(n)=Vec((1+x^5+x^10)*(1+x+x^2+x^3+x^4)*(1+x)/(1-43*x-43*x^2-43*x^3-43*x^4-43*x^5-43*x^6-43*x^7-43*x^8-43*x^9-43*x^10-43*x^11-43*x^12-43*x^13-43*x^14+946*x^15)+O(x^(n+1))) \\ _Charles R Greathouse IV_, Aug 14 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167855

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167855 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167855 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167855
