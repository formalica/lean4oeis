import LOEIS.A166.A166541.Defs

/-!
# A166541 — program transcriptions (`Equiv_1b7badd7945efa58`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(28*t^12 - 7*t^11 - 7*t^10 - 7*t^9 - 7*t^8 - 7*t^7 - 7*t^6 - 7*t^5 - 7*t^4 - 7*t^3 - 7*t^2 - 7*t + 1). From _G. C. Greubel_, Aug 23 2024: (Start) a(n) = 7*Sum_{j=1..11} a(n-j) - 28*a(n-13). G.f.: (1+x)*(1-x^12)/(1 - 8*x + 35*x^12 - 28*x^13). (End)` (gf-rational)
* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(28*t^12 - 7*t^11 - 7*t^10 - 7*t^9 - 7*t^8 - 7*t^7 - 7*t^6 - 7*t^5 - 7*t^4 - 7*t^3 - 7*t^2 - 7*t + 1). From _G. C. Greubel_, Aug 23 2024: (Start) a(n) = 7*Sum_{j=1..11} a(n-j) - 28*a(n-13). G.f.: (1+x)*(1-x^12)/(1 - 8*x + 35*x^12 - 28*x^13). (End)` (gf-factored)
* `%F a(n) = 7*Sum_{j=1..11} a(n-j) - 28*a(n-13).` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^12)/(1-8*t+35*t^12-28*t^13), {t, 0, 50}], t] (* _G. C. Greubel_, May 16 2016; Aug 23 2024 *)` (wolfram-series)
* `%T coxG[{12,28,-7, 30}]` (wolfram-coxG)
* `%O R<x>:=PowerSeriesRing(Integers(), 30); Coefficients(R!( (1+x)*(1-x^12)/(1-8*x+35*x^12-28*x^13) )); // _G. C. Greubel_, Aug 23 2024` (magma-series)
* `%O (PARI) a(n)=if(n,([0,1,0,0,0,0,0,0,0,0,0,0; 0,0,1,0,0,0,0,0,0,0,0,0; 0,0,0,1,0,0,0,0,0,0,0,0; 0,0,0,0,1,0,0,0,0,0,0,0; 0,0,0,0,0,1,0,0,0,0,0,0; 0,0,0,0,0,0,1,0,0,0,0,0; 0,0,0,0,0,0,0,1,0,0,0,0; 0,0,0,0,0,0,0,0,1,0,0,0; 0,0,0,0,0,0,0,0,0,1,0,0; 0,0,0,0,0,0,0,0,0,0,1,0; 0,0,0,0,0,0,0,0,0,0,0,1; -28,7,7,7,7,7,7,7,7,7,7,7]^(n-1)*[9;72;576;4608;36864;294912;2359296;18874368;150994944;1207959552;9663676416;77309411292])[1,1],1) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166541

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166541 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A166541 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166541
