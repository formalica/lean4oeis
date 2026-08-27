import LOEIS.A166.A166557.Defs

/-!
# A166557 — program transcriptions (`Equiv_bd4589ebb9f53b9b`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(55*t^12 - 10*t^11 - 10*t^10 - 10*t^9 - 10*t^8 - 10*t^7 - 10*t^6 - 10*t^5 - 10*t^4 - 10*t^3 - 10*t^2 - 10*t +1). From _G. C. Greubel_, Dec 03 2024: (Start) a(n) = 10*Sum_{j=1..11} a(n-j) - 55*a(n-12). G.f.: (1+t)*(1 - t^12)/(1 - 11*t + 65*t^12 - 55*t^13). (End)` (gf-rational)
* `%F G.f.: (t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(55*t^12 - 10*t^11 - 10*t^10 - 10*t^9 - 10*t^8 - 10*t^7 - 10*t^6 - 10*t^5 - 10*t^4 - 10*t^3 - 10*t^2 - 10*t +1). From _G. C. Greubel_, Dec 03 2024: (Start) a(n) = 10*Sum_{j=1..11} a(n-j) - 55*a(n-12). G.f.: (1+t)*(1 - t^12)/(1 - 11*t + 65*t^12 - 55*t^13). (End)` (gf-factored)
* `%F a(n) = 10*Sum_{j=1..11} a(n-j) - 55*a(n-12).` (recurrence)
* `%T CoefficientList[Series[(1+t)*(1-t^12)/(1-11*t+65*t^12-55*t^13), {t,0,50}], t]` (wolfram-series)
* `%T coxG[{12,55,-10}]` (wolfram-coxG)
* `%O (PARI) a(n)=if(n,([0,1,0,0,0,0,0,0,0,0,0,0; 0,0,1,0,0,0,0,0,0,0,0,0; 0,0,0,1,0,0,0,0,0,0,0,0; 0,0,0,0,1,0,0,0,0,0,0,0; 0,0,0,0,0,1,0,0,0,0,0,0; 0,0,0,0,0,0,1,0,0,0,0,0; 0,0,0,0,0,0,0,1,0,0,0,0; 0,0,0,0,0,0,0,0,1,0,0,0; 0,0,0,0,0,0,0,0,0,1,0,0; 0,0,0,0,0,0,0,0,0,0,1,0; 0,0,0,0,0,0,0,0,0,0,0,1; -55,10,10,10,10,10,10,10,10,10,10,10]^(n-1)*[12;132;1452;15972;175692;1932612;21258732;233846052;2572306572;28295372292;311249095212;3423740047266])[1,1],1) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166557

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166557 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166557 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166557
