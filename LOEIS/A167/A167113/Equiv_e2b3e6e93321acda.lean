import LOEIS.A167.A167113.Defs

/-!
# A167113 — program transcriptions (`Equiv_e2b3e6e93321acda`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(55*t^14 - 10*t^13 - 10*t^12 - 10*t^11 - 10*t^10 - 10*t^9 - 10*t^8 - 10*t^7 - 10*t^6 - 10*t^5 - 10*t^4 - 10*t^3 - 10*t^2 - 10*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/ (55*t^14 - 10*t^13 - 10*t^12 - 10*t^11 - 10*t^10 - 10*t^9 - 10*t^8 - 10*t^7 - 10*t^6 - 10*t^5 - 10*t^4 - 10*t^3 - 10*t^2 - 10*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Jun 03 2016 *)` (wolfram-series)
* `%O (PARI) first(n)=Vec((1+x^2+x^4+x^6+x^8+x^10+x^12)*(1+x)^2/(1-10*x-10*x^2-10*x^3-10*x^4-10*x^5-10*x^6-10*x^7-10*x^8-10*x^9-10*x^10-10*x^11-10*x^12-10*x^13+55*x^14)+O(x^(n+1))) \\ _Charles R Greathouse IV_, Jun 11 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167113

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167113 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167113 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167113
