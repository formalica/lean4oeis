import OEISLib.Coxeter

/-!
# A170407

Number of reduced words of length n in Coxeter group on 14 generators S_i with relations (S_i)^2 = (S_i S_j)^44 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=14` `r=44`. The rational generating function is ` (t^44 + 2t^{43}+…+1) / (78·t^44 - 12·(t^{43}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A170407

/-- Number of generators `g` of `A170407`. -/
abbrev gParam : Nat := 14

/-- Edge label `r` of `A170407`. -/
abbrev rParam : Nat := 44

/-- `C(g-1,2)` for `A170407`. -/
abbrev c1Param : Nat := 78

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 16

/-- Index type of `A170407` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A170407`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A170407

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A170407 : A170407.argType → A170407.retType := fun n =>
  OEISLib.Coxeter.coxSeq A170407.gParam A170407.rParam n

namespace A170407

/-- Relation that defines `A170407`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A170407 n) := rfl

/-- `A170407` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A170407

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A170407 n := rfl

/-- `A170407` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A170407 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A170407 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A170407
