import LOEIS.A166.A166427.Defs

/-!
# A166427 — program transcriptions (`Equiv_4cb4eb143b021a0e`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(496*t^11 - 31*t^10 - 31*t^9 - 31*t^8 - 31*t^7 - 31*t^6 - 31*t^5 - 31*t^4 - 31*t^3 - 31*t^2 - 31*t + 1).` (gf-rational)
* `%T With[{num=Total[2t^Range[10]]+t^11+1,den=Total[-31 t^Range[10]]+496t^11+ 1}, CoefficientList[Series[num/den,{t,0,30}],t]] (* _Harvey P. Dale_, Aug 16 2011 *)` (wolfram-series)
* `%T coxG[{11, 496, -31, 30}]` (wolfram-coxG)
* `%O (PARI) a(n)=if(n,([0,1,0,0,0,0,0,0,0,0,0; 0,0,1,0,0,0,0,0,0,0,0; 0,0,0,1,0,0,0,0,0,0,0; 0,0,0,0,1,0,0,0,0,0,0; 0,0,0,0,0,1,0,0,0,0,0; 0,0,0,0,0,0,1,0,0,0,0; 0,0,0,0,0,0,0,1,0,0,0; 0,0,0,0,0,0,0,0,1,0,0; 0,0,0,0,0,0,0,0,0,1,0; 0,0,0,0,0,0,0,0,0,0,1; -496,31,31,31,31,31,31,31,31,31,31]^(n-1)*[33;1056;33792;1081344;34603008;1107296256;35433480192;1133871366144;36283883716608;1161084278931456;37154696925806064])[1,1],1) \\ _Charles R Greathouse IV_, Jun 08 2026` (pari-vec)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A166427

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A166427 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A166427 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A166427
