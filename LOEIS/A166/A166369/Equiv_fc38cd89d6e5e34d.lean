import LOEIS.A166.A166369.Defs

/-!
# A166369 — program transcriptions (`Equiv_fc38cd89d6e5e34d`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(45*t^11 - 9*t^10 - 9*t^9 - 9*t^8 - 9*t^7 - 9*t^6 - 9*t^5 - 9*t^4 - 9*t^3 - 9*t^2 - 9*t + 1). From _G. C. Greubel_, Jul 23 2024: (Start) a(n) = 9*Sum_{j=1..10} a(n-j) - 45*a(n-11). G.f.: (1+t)*(1-t^11)/(1 - 10*t + 54*t^11 - 45*t^12). (End)` (gf-rational)
* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(45*t^11 - 9*t^10 - 9*t^9 - 9*t^8 - 9*t^7 - 9*t^6 - 9*t^5 - 9*t^4 - 9*t^3 - 9*t^2 - 9*t + 1). From _G. C. Greubel_, Jul 23 2024: (Start) a(n) = 9*Sum_{j=1..10} a(n-j) - 45*a(n-11). G.f.: (1+t)*(1-t^11)/(1 - 10*t + 54*t^11 - 45*t^12). (End)` (gf-factored)
* `%F a(n) = 9*Sum_{j=1..10} a(n-j) - 45*a(n-11).` (recurrence)
* `%T With[{p=45, q=9}, CoefficientList[Series[(1+t)*(1-t^11)/(1-(q+1)*t + (p+q)*t^11-p*t^12), {t,0,40}], t]] (* _G. C. Greubel_, May 10 2016; Jul 23 2024 *)` (wolfram-series)
* `%T coxG[{11,45,-9}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x+x^2+x^3+x^4+x^5+x^6+x^7+x^8+x^9+x^10)*(1+x)/(1-9*x-9*x^2-9*x^3-9*x^4-9*x^5-9*x^6-9*x^7-9*x^8-9*x^9-9*x^10+45*x^11)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166369

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166369 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166369 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166369
