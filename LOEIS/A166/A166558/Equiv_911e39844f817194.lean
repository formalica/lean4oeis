import LOEIS.A166.A166558.Defs

/-!
# A166558 — program transcriptions (`Equiv_911e39844f817194`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(66*t^12 - 11*t^11 - 11*t^10 - 11*t^9 - 11*t^8 - 11*t^7 - 11*t^6 - 11*t^5 - 11*t^4 - 11*t^3 - 11*t^2 - 11*t +1). From _G. C. Greubel_, Dec 03 2024: (Start) a(n) = 11*Sum_{j=1..11} a(n-j) - 66*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 12*x + 77*x^12 - 66*x^13). (End)` (gf-rational)
* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(66*t^12 - 11*t^11 - 11*t^10 - 11*t^9 - 11*t^8 - 11*t^7 - 11*t^6 - 11*t^5 - 11*t^4 - 11*t^3 - 11*t^2 - 11*t +1). From _G. C. Greubel_, Dec 03 2024: (Start) a(n) = 11*Sum_{j=1..11} a(n-j) - 66*a(n-12). G.f.: (1+x)*(1-x^12)/(1 - 12*x + 77*x^12 - 66*x^13). (End)` (gf-factored)
* `%F a(n) = 11*Sum_{j=1..11} a(n-j) - 66*a(n-12).` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^12)/(1-12*t+77*t^12-66*t^13), {t,0,50}], t] (* _G. C. Greubel_, May 17 2016; Dec 03 2024 *)` (wolfram-series)
* `%T coxG[{12,66,-11}]` (wolfram-coxG)
* `%O (PARI) a(n)=if(n,([0,1,0,0,0,0,0,0,0,0,0,0; 0,0,1,0,0,0,0,0,0,0,0,0; 0,0,0,1,0,0,0,0,0,0,0,0; 0,0,0,0,1,0,0,0,0,0,0,0; 0,0,0,0,0,1,0,0,0,0,0,0; 0,0,0,0,0,0,1,0,0,0,0,0; 0,0,0,0,0,0,0,1,0,0,0,0; 0,0,0,0,0,0,0,0,1,0,0,0; 0,0,0,0,0,0,0,0,0,1,0,0; 0,0,0,0,0,0,0,0,0,0,1,0; 0,0,0,0,0,0,0,0,0,0,0,1; -66,11,11,11,11,11,11,11,11,11,11,11]^(n-1)*[13;156;1872;22464;269568;3234816;38817792;465813504;5589762048;67077144576;804925734912;9659108818866])[1,1],1) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166558

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166558 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166558 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166558
