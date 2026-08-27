import LOEIS.A167.A167880.Defs

/-!
# A167880 — program transcriptions (`Equiv_b6bd73c5840fe0fc`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(1176*t^15 - 48*t^14 - 48*t^13 - 48*t^12 - 48*t^11 - 48*t^10 - 48*t^9 - 48*t^8 - 48*t^7 - 48*t^6 - 48*t^5 - 48*t^4 - 48*t^3 - 48*t^2 - 48*t + 1).` (gf-rational)
* `%T With[{num=Total[2t^Range[14]]+t^15+1,den=Total[-48 t^Range[14]]+ 1176t^15+1},CoefficientList[Series[num/den,{t,0,20}],t]] (* _Harvey P. Dale_, Aug 22 2011 *)` (wolfram-series)
* `%O (PARI) first(n)=Vec((1+x^5+x^10)*(1+x+x^2+x^3+x^4)*(1+x)/(1-48*x-48*x^2-48*x^3-48*x^4-48*x^5-48*x^6-48*x^7-48*x^8-48*x^9-48*x^10-48*x^11-48*x^12-48*x^13-48*x^14+1176*x^15)+O(x^(n+1))) \\ _Charles R Greathouse IV_, Aug 14 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167880

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167880 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A167880 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167880
