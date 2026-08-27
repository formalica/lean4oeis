import OEISLib.Coxeter

/-!
# A170278

Number of reduced words of length n in Coxeter group on 29 generators S_i with relations (S_i)^2 = (S_i S_j)^41 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=29` `r=41`. The rational generating function is ` (t^41 + 2t^{40}+…+1) / (378·t^41 - 27·(t^{40}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A170278

/-- Number of generators `g` of `A170278`. -/
abbrev gParam : Nat := 29

/-- Edge label `r` of `A170278`. -/
abbrev rParam : Nat := 41

/-- `C(g-1,2)` for `A170278`. -/
abbrev c1Param : Nat := 378

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A170278` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A170278`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A170278

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A170278 : A170278.argType → A170278.retType := fun n =>
  OEISLib.Coxeter.coxSeq A170278.gParam A170278.rParam n

namespace A170278

/-- Relation that defines `A170278`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A170278 n) := rfl

/-- `A170278` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A170278

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A170278 n := rfl

/-- `A170278` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A170278 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A170278 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A170278
