import LOEIS.A164.A164548.Defs

/-!
# A164548 — program transcriptions (`Equiv_3c0a91e38c56e33e`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(36*t^7 - 8*t^6 - 8*t^5 - 8*t^4 - 8*t^3 - 8*t^2 - 8*t + 1). G.f.: (1+t)*(1-t^7)/(1 -9*t +44*t^7 -36*t^8). - _G. C. Greubel_, Jul 17 2021` (gf-rational)
* `%F G.f.: (t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(36*t^7 - 8*t^6 - 8*t^5 - 8*t^4 - 8*t^3 - 8*t^2 - 8*t + 1). G.f.: (1+t)*(1-t^7)/(1 -9*t +44*t^7 -36*t^8). - _G. C. Greubel_, Jul 17 2021` (gf-factored)
* `%T CoefficientList[Series[(1+t)*(1-t^7)/(1 -9*t +44*t^7 -36*t^8), {t,0,30}], t] (* or *)` (wolfram-series)
* `%T coxG[{7, 36, -8, 30}]` (wolfram-coxG)
* `%O (PARI) a(n)=if(n,([0,1,0,0,0,0,0; 0,0,1,0,0,0,0; 0,0,0,1,0,0,0; 0,0,0,0,1,0,0; 0,0,0,0,0,1,0; 0,0,0,0,0,0,1; -36,8,8,8,8,8,8]^(n-1)*[10;90;810;7290;65610;590490;5314365])[1,1],1) \\ _Charles R Greathouse IV_, Jun 05 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A164548

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A164548 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A164548 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A164548
