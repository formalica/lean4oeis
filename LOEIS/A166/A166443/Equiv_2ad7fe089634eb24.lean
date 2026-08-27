import LOEIS.A166.A166443.Defs

/-!
# A166443 — program transcriptions (`Equiv_2ad7fe089634eb24`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(1128*t^11 - 47*t^10 - 47*t^9 - 47*t^8 - 47*t^7 - 47*t^6 - 47*t^5 - 47*t^4 - 47*t^3 - 47*t^2 - 47*t + 1). From _G. C. Greubel_, Jul 27 2024: (Start) a(n) = 47*Sum_{j=1..10} a(n-j) - 1128*a(n-11). G.f.: (1+x)*(1-x^11)/(1 - 48*x + 1175*x^11 - 1128*x^12). (End)` (gf-rational)
* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(1128*t^11 - 47*t^10 - 47*t^9 - 47*t^8 - 47*t^7 - 47*t^6 - 47*t^5 - 47*t^4 - 47*t^3 - 47*t^2 - 47*t + 1). From _G. C. Greubel_, Jul 27 2024: (Start) a(n) = 47*Sum_{j=1..10} a(n-j) - 1128*a(n-11). G.f.: (1+x)*(1-x^11)/(1 - 48*x + 1175*x^11 - 1128*x^12). (End)` (gf-factored)
* `%F a(n) = 47*Sum_{j=1..10} a(n-j) - 1128*a(n-11).` (recurrence)
* `%T With[{num=Total[2t^Range[10]]+t^11+1,den=Total[-47 t^Range[10]]+ 1128t^11+ 1}, CoefficientList[Series[num/den,{t,0,20}],t]] (* _Harvey P. Dale_, Aug 29 2011 *)` (wolfram-series)
* `%T coxG[{11, 1128, -47, 30}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x+x^2+x^3+x^4+x^5+x^6+x^7+x^8+x^9+x^10)*(1+x)/(1-47*x-47*x^2-47*x^3-47*x^4-47*x^5-47*x^6-47*x^7-47*x^8-47*x^9-47*x^10+1128*x^11)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166443

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166443 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166443 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166443
