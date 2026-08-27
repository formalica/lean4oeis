import LOEIS.A167.A167644.Defs

/-!
# A167644 — program transcriptions (`Equiv_51c6e4586957bf65`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(1035*t^14 - 45*t^13 - 45*t^12 - 45*t^11 - 45*t^10 - 45*t^9 - 45*t^8 - 45*t^7 - 45*t^6 - 45*t^5 - 45*t^4 - 45*t^3 - 45*t^2 - 45*t + 1).` (gf-rational)
* `%T CoefficientList[Series[(t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/ (1035*t^14 - 45*t^13 - 45*t^12 - 45*t^11 - 45*t^10 - 45*t^9 - 45*t^8 - 45*t^7 - 45*t^6 - 45*t^5 - 45*t^4 - 45*t^3 - 45*t^2 - 45*t + 1), {t, 0, 50}], t] (* _G. C. Greubel_, Jun 18 2016 *)` (wolfram-series)
* `%T coxG[{14,1035,-45}]` (wolfram-coxG)
* `%O (PARI) first(n)=Vec((1+x^2+x^4+x^6+x^8+x^10+x^12)*(1+x)^2/(1-45*x-45*x^2-45*x^3-45*x^4-45*x^5-45*x^6-45*x^7-45*x^8-45*x^9-45*x^10-45*x^11-45*x^12-45*x^13+1035*x^14)+O(x^(n+1))) \\ _Charles R Greathouse IV_, Jun 11 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167644

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167644 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167644 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167644
