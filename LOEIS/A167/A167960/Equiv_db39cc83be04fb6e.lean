import LOEIS.A167.A167960.Defs

/-!
# A167960 — program transcriptions (`Equiv_db39cc83be04fb6e`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/( 903*t^16 - 42*t^15 - 42*t^14 - 42*t^13 - 42*t^12 - 42*t^11 - 42*t^10 - 42*t^9 - 42*t^8 - 42*t^7 - 42*t^6 - 42*t^5 - 42*t^4 - 42*t^3 - 42*t^2 - 42*t + 1). From _G. C. Greubel_, Apr 27 2023: (Start) G.f.: (1 + x)*(1 + x^16)/(1 - 43*x + 903*x^16 - 861*x^17). a(n) = 42*Sum_{k=1..m-1} a(n-k) - 903*a(n-m). (End)` (gf-rational)
* `%F a(n) = 42*Sum_{k=1..m-1} a(n-k) - 903*a(n-m). (End)` (recurrence)
* `%T CoefficientList[Series[(1+x)*(1+x^16)/(1-43*x+903*x^16-861*x^17), {x, 0, 50}], x] (* _G. C. Greubel_, Jul 02 2016; Apr 27 2023 *)` (wolfram-series)
* `%T coxG[{16,903,-42}]` (wolfram-coxG)
* `%O (Magma) R<x>:=PowerSeriesRing(Integers(), 40); Coefficients(R!( (1+x)*(1+x^16)/(1-43*x+903*x^16-861*x^17) )); // _G. C. Greubel_, Apr 27 2023` (magma-series)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A167960

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam 50

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam 50 := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A167960 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam 50).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam 50 n h'
  have h2 : A167960 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A167960
