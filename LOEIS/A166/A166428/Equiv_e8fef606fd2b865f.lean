import LOEIS.A166.A166428.Defs

/-!
# A166428 — program transcriptions (`Equiv_e8fef606fd2b865f`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(528*t^11 - 32*t^10 - 32*t^9 - 32*t^8 - 32*t^7 - 32*t^6 - 32*t^5 - 32*t^4 - 32*t^3 - 32*t^2 - 32*t + 1). From _G. C. Greubel_, Jul 25 2024: (Start) a(n) = 32*Sum_{j=1..10} a(n-j) - 528*a(n-11). G.f.: (1+x)*(1-x^11)/(1 - 33*x + 560*x^11 - 528*x^12). (End)` (gf-rational)
* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(528*t^11 - 32*t^10 - 32*t^9 - 32*t^8 - 32*t^7 - 32*t^6 - 32*t^5 - 32*t^4 - 32*t^3 - 32*t^2 - 32*t + 1). From _G. C. Greubel_, Jul 25 2024: (Start) a(n) = 32*Sum_{j=1..10} a(n-j) - 528*a(n-11). G.f.: (1+x)*(1-x^11)/(1 - 33*x + 560*x^11 - 528*x^12). (End)` (gf-factored)
* `%F a(n) = 32*Sum_{j=1..10} a(n-j) - 528*a(n-11).` (recurrence)
* `%T With[{p=528, q=32}, CoefficientList[Series[(1+t)*(1-t^11)/(1-(q+1)*t + (p+q)*t^11-p*t^12), {t,0,40}], t]] (* _G. C. Greubel_, May 13 2016; Jul 25 2024 *)` (wolfram-series)
* `%T coxG[{11, 528, -32, 30}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x+x^2+x^3+x^4+x^5+x^6+x^7+x^8+x^9+x^10)*(1+x)/(1-32*x-32*x^2-32*x^3-32*x^4-32*x^5-32*x^6-32*x^7-32*x^8-32*x^9-32*x^10+528*x^11)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166428

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166428 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166428 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166428
