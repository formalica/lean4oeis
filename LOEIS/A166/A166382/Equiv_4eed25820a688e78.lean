import LOEIS.A166.A166382.Defs

/-!
# A166382 — program transcriptions (`Equiv_4eed25820a688e78`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(91*t^11 - 13*t^10 - 13*t^9 - 13*t^8 - 13*t^7 - 13*t^6 - 13*t^5 - 13*t^4 - 13*t^3 - 13*t^2 - 13*t + 1). From _G. C. Greubel_, Jul 23 2024: (Start) a(n) = 13*Sum_{j=1..10} a(n-j) - 91*a(n-11). G.f.: (1+x)*(1 - x^11)/(1 - 14*x + 104*x^11 - 91*x^12). (End)` (gf-rational)
* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(91*t^11 - 13*t^10 - 13*t^9 - 13*t^8 - 13*t^7 - 13*t^6 - 13*t^5 - 13*t^4 - 13*t^3 - 13*t^2 - 13*t + 1). From _G. C. Greubel_, Jul 23 2024: (Start) a(n) = 13*Sum_{j=1..10} a(n-j) - 91*a(n-11). G.f.: (1+x)*(1 - x^11)/(1 - 14*x + 104*x^11 - 91*x^12). (End)` (gf-factored)
* `%F a(n) = 13*Sum_{j=1..10} a(n-j) - 91*a(n-11).` (recurrence)
* `%T With[{a=91, b=13}, CoefficientList[Series[(1+t)*(1-t^11)/(1-(b+1)*t +(a+b)*t^11-a*t^12), {t,0,40}], t]] (* _G. C. Greubel_, May 10 2016; Jul 23 2024 *)` (wolfram-series)
* `%T coxG[{11,91,-13}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x+x^2+x^3+x^4+x^5+x^6+x^7+x^8+x^9+x^10)*(1+x)/(1-13*x-13*x^2-13*x^3-13*x^4-13*x^5-13*x^6-13*x^7-13*x^8-13*x^9-13*x^10+91*x^11)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166382

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166382 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166382 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166382
