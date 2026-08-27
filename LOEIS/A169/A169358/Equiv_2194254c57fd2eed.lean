import LOEIS.A169.A169358.Defs

/-!
# A169358 — program transcriptions (`Equiv_2194254c57fd2eed`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%F G.f.: (t^31 + 2*t^30 + 2*t^29 + 2*t^28 + 2*t^27 + 2*t^26 + 2*t^25 + 2*t^24 + 2*t^23 + 2*t^22 + 2*t^21 + 2*t^20 + 2*t^19 + 2*t^18 + 2*t^17 + 2*t^16 + 2*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 2*t^11 + 2*t^10 + 2*t^9 + 2*t^8 + 2*t^7 + 2*t^6 + 2*t^5 + 2*t^4 + 2*t^3 + 2*t^2 + 2*t + 1)/(28*t^31 - 7*t^30 - 7*t^29 - 7*t^28 - 7*t^27 - 7*t^26 - 7*t^25 - 7*t^24 - 7*t^23 - 7*t^22 - 7*t^21 - 7*t^20 - 7*t^19 - 7*t^18 - 7*t^17 - 7*t^16 - 7*t^15 - 7*t^14 - 7*t^13 - 7*t^12 - 7*t^11 - 7*t^10 - 7*t^9 - 7*t^8 - 7*t^7 - 7*t^6 - 7*t^5 - 7*t^4 - 7*t^3 - 7*t^2 - 7*t + 1). a(n) = -28*a(n-31) + 7*Sum_{k=1..30} a(n-k). - _Wesley Ivan Hurt_, Apr 26 2021` (gf-rational)
* `%F a(n) = -28*a(n-31) + 7*Sum_{k=1..30} a(n-k). - _Wesley Ivan Hurt_, Apr 26 2021` (recurrence)

All delegate to the shared library `OEISLib.Coxeter.coxSeq` / `coeffsUpTo`; bridges are `rfl`.
-/

namespace A169358

/-- Alternative definition transcribed from the `%F`/`%t`/`%o` program snippets (truncated coefficient list). -/
def formula : List Nat := OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound

/-- `formula` is the generic truncated enumeration (definitionally). -/
theorem formula_rfl : formula = OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound := rfl

/-- **formula_eq**: reading `formula` position by position is exactly the main definition (when within bounds). -/
theorem formula_eq (n : Nat) (h : n < formula.length) :
    formula[n]'h = A169358 n := by
  have h' : n < (OEISLib.Coxeter.coeffsUpTo gParam rParam searchBound).length := by
    simpa [formula] using h
  have h1 := OEISLib.Coxeter.coeffsUpTo_getElem gParam rParam searchBound n h'
  have h2 : A169358 n = OEISLib.Coxeter.coxSeq gParam rParam n := rfl
  rw [h2]
  simpa [formula] using h1

end A169358
