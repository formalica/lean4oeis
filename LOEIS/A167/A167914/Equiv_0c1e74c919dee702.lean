import LOEIS.A167.A167914.Defs

/-!
# A167914 — program transcriptions (`Equiv_0c1e74c919dee702`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 45*t^16 - 9*t^15 - 9*t^14 - 9*t^13 - 9*t^12 - 9*t^11 - 9*t^10 - 9*t^9 - 9*t^8 - 9*t^7 - 9*t^6 - 9*t^5 - 9*t^4 - 9*t^3 - 9*t^2 - 9*t + 1). From _G. C. Greubel_, Dec 04 2024: (Start) a(n) = 9*Sum_{j=1..15} a(n-j) - 45*a(n-16). G.f.: (1+x)*(1-x^16)/(1 - 10*x + 54*x^16 - 45*x^17). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 45*t^16 - 9*t^15 - 9*t^14 - 9*t^13 - 9*t^12 - 9*t^11 - 9*t^10 - 9*t^9 - 9*t^8 - 9*t^7 - 9*t^6 - 9*t^5 - 9*t^4 - 9*t^3 - 9*t^2 - 9*t + 1). From _G. C. Greubel_, Dec 04 2024: (Start) a(n) = 9*Sum_{j=1..15} a(n-j) - 45*a(n-16). G.f.: (1+x)*(1-x^16)/(1 - 10*x + 54*x^16 - 45*x^17). (End)` (gf-factored)
* `%F a(n) = 9*Sum_{j=1..15} a(n-j) - 45*a(n-16).` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^16)/(1-10*t+54*t^16-45*t^17), {t,0,50}], t] (* _G. C. Greubel_, Jul 01 2016; Dec 04 2024 *)` (wolfram-series)
* `%T coxG[{16,45,-9}]` (wolfram-coxG)
* `%O (PARI) Vec((x^16+2*x^15+2*x^14+2*x^13+2*x^12+2*x^11+2*x^10+2*x^9+2*x^8+2*x^7+2*x^6+2*x^5+2*x^4+2*x^3+2*x^2+2*x+1)/(45*x^16-9*x^15-9*x^14-9*x^13-9*x^12-9*x^11-9*x^10-9*x^9-9*x^8-9*x^7-9*x^6-9*x^5-9*x^4-9*x^3-9*x^2-9*x+1)+O(x^99)) \\ _Charles R Greathouse IV_, May 15 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167914

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167914 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A167914 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167914
