import LOEIS.A167.A167785.Defs

/-!
# A167785 — program transcriptions (`Equiv_3753bd985264dd0a`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(528*t^15 - 32*t^14 - 32*t^13 - 32*t^12 - 32*t^11 - 32*t^10 - 32*t^9 - 32*t^8 - 32*t^7 - 32*t^6 - 32*t^5 - 32*t^4 - 32*t^3 - 32*t^2 - 32*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(528*t^15 - 32*t^14 - 32*t^13 - 32*t^12 - 32*t^11 - 32*t^10 - 32*t^9 - 32*t^8 - 32*t^7 - 32*t^6 - 32*t^5 - 32*t^4 - 32*t^3 - 32*t^2 - 32*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Jun 27 2016 *)` (wolfram-series)
* `%O (PARI) first(n)=Vec((1+x^5+x^10)*(1+x+x^2+x^3+x^4)*(1+x)/(1-32*x-32*x^2-32*x^3-32*x^4-32*x^5-32*x^6-32*x^7-32*x^8-32*x^9-32*x^10-32*x^11-32*x^12-32*x^13-32*x^14+528*x^15)+O(x^(n+1))) \\ _Charles R Greathouse IV_, Jun 13 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167785

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167785 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167785 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167785
