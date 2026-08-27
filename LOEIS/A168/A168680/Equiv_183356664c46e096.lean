import LOEIS.A168.A168680.Defs

/-!
# A168680 — program transcriptions (`Equiv_183356664c46e096`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + t^15 + t^14 + t^13 + t^12 + t^11 + t^10 + t^9 + t^8 + t^7 + t^6 + t^5 + t^4 + t^3 + t^2 + t + 1)/(t^16 - 2*t^15 + t^14 - 2*t^13 + t^12 - 2*t^11 + t^10 - 2*t^9 + t^8 - 2*t^7 + t^6 - 2*t^5 + t^4 - 2*t^3 + t^2 - 2*t + 1). G.f.: (1+t)*(1-t^17)/(1 -2*t +2*t^17 -t^18). - _G. C. Greubel_, Feb 22 2021` (gf-rational)
* `%F G.f.: (t^16 + t^15 + t^14 + t^13 + t^12 + t^11 + t^10 + t^9 + t^8 + t^7 + t^6 + t^5 + t^4 + t^3 + t^2 + t + 1)/(t^16 - 2*t^15 + t^14 - 2*t^13 + t^12 - 2*t^11 + t^10 - 2*t^9 + t^8 - 2*t^7 + t^6 - 2*t^5 + t^4 - 2*t^3 + t^2 - 2*t + 1). G.f.: (1+t)*(1-t^17)/(1 -2*t +2*t^17 -t^18). - _G. C. Greubel_, Feb 22 2021` (gf-factored)
* `%T CoefficientList[Series[(1+t)*(1-t^17)/(1 -2*t +2*t^17 -t^18), {t, 0, 40}], t] (* _G. C. Greubel_, Jul 29 2016, Feb 22 2021 *)` (wolfram-series)
* `%O (PARI) Vec(Pol(vector(17,i,1))/Pol(vector(17,i,if(i%2,1,-2)))+O(x^99)) \\ _Charles R Greathouse IV_, Jul 30 2016` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A168680

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 40

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 40 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A168680 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 40).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 40 n h'
  have h2 : A168680 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A168680
