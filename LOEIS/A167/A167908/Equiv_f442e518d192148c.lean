import LOEIS.A167.A167908.Defs

/-!
# A167908 — program transcriptions (`Equiv_f442e518d192148c`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 36*t^16 - 8*t^15 - 8*t^14 - 8*t^13 - 8*t^12 - 8*t^11 - 8*t^10 - 8*t^9 - 8*t^8 - 8*t^7 - 8*t^6 - 8*t^5 - 8*t^4 - 8*t^3 - 8*t^2 - 8*t + 1). From _G. C. Greubel_, Jul 23 2024: (Start) a(n) = 8*Sum_{j=1..15} a(n-j) - 36*a(n-16). G.f.: (1+t)*(1 - t^16)/(1 - 9*t + 44*t^16 - 36*t^17). (End)` (gf-rational)
* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 36*t^16 - 8*t^15 - 8*t^14 - 8*t^13 - 8*t^12 - 8*t^11 - 8*t^10 - 8*t^9 - 8*t^8 - 8*t^7 - 8*t^6 - 8*t^5 - 8*t^4 - 8*t^3 - 8*t^2 - 8*t + 1). From _G. C. Greubel_, Jul 23 2024: (Start) a(n) = 8*Sum_{j=1..15} a(n-j) - 36*a(n-16). G.f.: (1+t)*(1 - t^16)/(1 - 9*t + 44*t^16 - 36*t^17). (End)` (gf-factored)
* `%F a(n) = 8*Sum_{j=1..15} a(n-j) - 36*a(n-16).` (recurrence)
* `%T With[{a=36, b=8}, CoefficientList[Series[(1+t)*(1-t^16)/(1-(b+1)*t +(a + b)*t^16 -a*t^17), {t,0,40}], t]] (* _G. C. Greubel_, Jul 01 2016; Jul 23 2024 *)` (wolfram-series)
* `%T coxG[{16,36,-8}]` (wolfram-coxG)
* `%O (PARI) Vec((x^16+2*x^15+2*x^14+2*x^13+2*x^12+2*x^11+2*x^10+2*x^9+2*x^8+2*x^7+2*x^6+2*x^5+2*x^4+2*x^3+2*x^2+2*x+1)/(36*x^16-8*x^15-8*x^14-8*x^13-8*x^12-8*x^11-8*x^10-8*x^9-8*x^8-8*x^7-8*x^6-8*x^5-8*x^4-8*x^3-8*x^2-8*x+1)+O(x^99)) \\ _Charles R Greathouse IV_, May 15 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167908

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167908 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A167908 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167908
