import OEISLib.Coxeter

/-!
# A170549

Number of reduced words of length n in Coxeter group on 12 generators S_i with relations (S_i)^2 = (S_i S_j)^47 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=12` `r=47`. The rational generating function is ` (t^47 + 2t^{46}+…+1) / (55·t^47 - 10·(t^{46}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A170549

/-- Number of generators `g` of `A170549`. -/
abbrev gParam : Nat := 12

/-- Edge label `r` of `A170549`. -/
abbrev rParam : Nat := 47

/-- `C(g-1,2)` for `A170549`. -/
abbrev c1Param : Nat := 55

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 17

/-- Index type of `A170549` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A170549`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A170549

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A170549 : A170549.argType → A170549.retType := fun n =>
  OEISLib.Coxeter.coxSeq A170549.gParam A170549.rParam n

namespace A170549

/-- Relation that defines `A170549`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A170549 n) := rfl

/-- `A170549` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A170549

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A170549 n := rfl

/-- `A170549` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A170549 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A170549 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A170549
