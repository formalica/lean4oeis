import LOEIS.A166.A166426.Defs

/-!
# A166426 — program transcriptions (`Equiv_aec65b41cac164ad`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(465*t^11 - 30*t^10 - 30*t^9 - 30*t^8 - 30*t^7 - 30*t^6 - 30*t^5 - 30*t^4 - 30*t^3 - 30*t^2 - 30*t + 1). From _G. C. Greubel_, Jul 25 2024: (Start) a(n) = 30*Sum_{j=1..10} a(n-j) - 465*a(n-11). G.f.: (1+x)*(1-x^11)/(1 - 31*x + 495*x^11 - 465*x^12). (End)` (gf-rational)
* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(465*t^11 - 30*t^10 - 30*t^9 - 30*t^8 - 30*t^7 - 30*t^6 - 30*t^5 - 30*t^4 - 30*t^3 - 30*t^2 - 30*t + 1). From _G. C. Greubel_, Jul 25 2024: (Start) a(n) = 30*Sum_{j=1..10} a(n-j) - 465*a(n-11). G.f.: (1+x)*(1-x^11)/(1 - 31*x + 495*x^11 - 465*x^12). (End)` (gf-factored)
* `%F a(n) = 30*Sum_{j=1..10} a(n-j) - 465*a(n-11).` (recurrence)
* `%T coxG[{11,465,-30}]` (wolfram-coxG)
* `%T With[{p=465, q=30}, CoefficientList[Series[(1+t)*(1-t^11)/(1-(q+1)*t + (p+q)*t^11-p*t^12), {t,0,40}], t]] (* _G. C. Greubel_, May 13 2016; Jul 25 2024 *)` (wolfram-series)
* `%O (PARI) Vec((1+x+x^2+x^3+x^4+x^5+x^6+x^7+x^8+x^9+x^10)*(1+x)/(1-30*x-30*x^2-30*x^3-30*x^4-30*x^5-30*x^6-30*x^7-30*x^8-30*x^9-30*x^10+465*x^11)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166426

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166426 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166426 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166426
