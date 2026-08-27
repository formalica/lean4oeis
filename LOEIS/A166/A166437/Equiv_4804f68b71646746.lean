import LOEIS.A166.A166437.Defs

/-!
# A166437 — program transcriptions (`Equiv_4804f68b71646746`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(861*t^11 - 41*t^10 - 41*t^9 - 41*t^8 - 41*t^7 - 41*t^6 - 41*t^5 - 41*t^4 - 41*t^3 - 41*t^2 - 41*t + 1). a(n) = -861*a(n-11) + 41*Sum_{k=1..10} a(n-k). - _Wesley Ivan Hurt_, Mar 17 2023 G.f.: (1+x)*(1-x^11)/(1 - 42*x + 902*x^11 - 861*x^12). - _G. C. Greubel_, Jul 26 2024` (gf-rational)
* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(861*t^11 - 41*t^10 - 41*t^9 - 41*t^8 - 41*t^7 - 41*t^6 - 41*t^5 - 41*t^4 - 41*t^3 - 41*t^2 - 41*t + 1). a(n) = -861*a(n-11) + 41*Sum_{k=1..10} a(n-k). - _Wesley Ivan Hurt_, Mar 17 2023 G.f.: (1+x)*(1-x^11)/(1 - 42*x + 902*x^11 - 861*x^12). - _G. C. Greubel_, Jul 26 2024` (gf-factored)
* `%F a(n) = -861*a(n-11) + 41*Sum_{k=1..10} a(n-k). - _Wesley Ivan Hurt_, Mar 17 2023` (recurrence)
* `%T With[{p=861, q=41}, CoefficientList[Series[(1+t)*(1-t^11)/(1 - (q+1)*t + (p+q)*t^11 - p*t^12), {t,0,40}], t]] (* _G. C. Greubel_, May 14 2016; Jul 26 2024 *)` (wolfram-series)
* `%T coxG[{11, 861, -41, 30}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x+x^2+x^3+x^4+x^5+x^6+x^7+x^8+x^9+x^10)*(1+x)/(1-41*x-41*x^2-41*x^3-41*x^4-41*x^5-41*x^6-41*x^7-41*x^8-41*x^9-41*x^10+861*x^11)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166437

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166437 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166437 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166437
