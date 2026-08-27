import LOEIS.A166.A166442.Defs

/-!
# A166442 — program transcriptions (`Equiv_b42e8d7620894d59`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(1081*t^11 - 46*t^10 - 46*t^9 - 46*t^8 - 46*t^7 - 46*t^6 - 46*t^5 - 46*t^4 - 46*t^3 - 46*t^2 - 46*t + 1). From _G. C. Greubel_, Jul 26 2024: (Start) a(n) = 46*Sum_{j=1..10} a(n-j) - 1081*a(n-11). G.f.: (1+x)*(1-x^11)/(1 - 47*x + 1127*x^11 - 1081*x^12). (End)` (gf-rational)
* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(1081*t^11 - 46*t^10 - 46*t^9 - 46*t^8 - 46*t^7 - 46*t^6 - 46*t^5 - 46*t^4 - 46*t^3 - 46*t^2 - 46*t + 1). From _G. C. Greubel_, Jul 26 2024: (Start) a(n) = 46*Sum_{j=1..10} a(n-j) - 1081*a(n-11). G.f.: (1+x)*(1-x^11)/(1 - 47*x + 1127*x^11 - 1081*x^12). (End)` (gf-factored)
* `%F a(n) = 46*Sum_{j=1..10} a(n-j) - 1081*a(n-11).` (recurrence)
* `%T With[{num=Total[2t^Range[10] ]+t^11+1,den=Total[-46 t^Range[10]]+ 1081t^11+ 1}, CoefficientList[Series[num/den,{t,0,30}],t]] (* _Harvey P. Dale_, Jul 21 2011 *)` (wolfram-series)
* `%T coxG[{11, 1081, -46, 30}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x+x^2+x^3+x^4+x^5+x^6+x^7+x^8+x^9+x^10)*(1+x)/(1-46*x-46*x^2-46*x^3-46*x^4-46*x^5-46*x^6-46*x^7-46*x^8-46*x^9-46*x^10+1081*x^11)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166442

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166442 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166442 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166442
