import LOEIS.A166.A166431.Defs

/-!
# A166431 — program transcriptions (`Equiv_ee7879a5a5c9881f`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(630*t^11 - 35*t^10 - 35*t^9 - 35*t^8 - 35*t^7 - 35*t^6 - 35*t^5 - 35*t^4 - 35*t^3 - 35*t^2 - 35*t + 1). From _G. C. Greubel_, Jul 25 2024: (Start) a(n) = 35*Sum_{j=1..10} a(n-j) - 630*a(n-11). G.f.: (1+x)*(1-x^11)/(1 - 36*x + 665*x^11 - 630*x^12). (End)` (gf-rational)
* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(630*t^11 - 35*t^10 - 35*t^9 - 35*t^8 - 35*t^7 - 35*t^6 - 35*t^5 - 35*t^4 - 35*t^3 - 35*t^2 - 35*t + 1). From _G. C. Greubel_, Jul 25 2024: (Start) a(n) = 35*Sum_{j=1..10} a(n-j) - 630*a(n-11). G.f.: (1+x)*(1-x^11)/(1 - 36*x + 665*x^11 - 630*x^12). (End)` (gf-factored)
* `%F a(n) = 35*Sum_{j=1..10} a(n-j) - 630*a(n-11).` (recurrence)
* `%T With[{p=630, q=35}, CoefficientList[Series[(1+t)*(1-t^11)/(1-(q+1)*t + (p+q)*t^11-p*t^12), {t,0,40}], t]] (* _G. C. Greubel_, May 14 2016; Jul 25 2024 *)` (wolfram-series)
* `%T coxG[{11, 630, -35. 30}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x+x^2+x^3+x^4+x^5+x^6+x^7+x^8+x^9+x^10)*(1+x)/(1-35*x-35*x^2-35*x^3-35*x^4-35*x^5-35*x^6-35*x^7-35*x^8-35*x^9-35*x^10+630*x^11)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166431

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166431 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166431 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166431
