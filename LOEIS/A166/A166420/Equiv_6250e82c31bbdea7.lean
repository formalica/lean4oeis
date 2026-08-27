import LOEIS.A166.A166420.Defs

/-!
# A166420 — program transcriptions (`Equiv_6250e82c31bbdea7`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(300*t^11 - 24*t^10 - 24*t^9 - 24*t^8 - 24*t^7 - 24*t^6 - 24*t^5 - 24*t^4 - 24*t^3 - 24*t^2 - 24*t + 1). From _G. C. Greubel_, Jan 17 2023: (Start) a(n) = 24*Sum_{j=1..10} a(n-j) - 300*a(n-11). G.f.: (1+x)*(1-x^11)/(1 - 25*x + 324*x^11 - 300*x^12). (End)` (gf-rational)
* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(300*t^11 - 24*t^10 - 24*t^9 - 24*t^8 - 24*t^7 - 24*t^6 - 24*t^5 - 24*t^4 - 24*t^3 - 24*t^2 - 24*t + 1). From _G. C. Greubel_, Jan 17 2023: (Start) a(n) = 24*Sum_{j=1..10} a(n-j) - 300*a(n-11). G.f.: (1+x)*(1-x^11)/(1 - 25*x + 324*x^11 - 300*x^12). (End)` (gf-factored)
* `%F a(n) = 24*Sum_{j=1..10} a(n-j) - 300*a(n-11).` (recurrence)
* `%T With[{p=300, q=24}, CoefficientList[Series[(1+t)*(1-t^11)/(1-(q+1)*t + (p+q)*t^11-p*t^12), {t,0,40}], t]] (* _G. C. Greubel_, May 13 2016; Jul 25 2024 *)` (wolfram-series)
* `%T coxG[{11,300,-24}]` (wolfram-coxG)
* `%O (PARI) Vec((1+x+x^2+x^3+x^4+x^5+x^6+x^7+x^8+x^9+x^10)*(1+x)/(1-24*x-24*x^2-24*x^3-24*x^4-24*x^5-24*x^6-24*x^7-24*x^8-24*x^9-24*x^10+300*x^11)+O(x^99)) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166420

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166420 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166420 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166420
