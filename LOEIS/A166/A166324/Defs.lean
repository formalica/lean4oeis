import OEISLib.Coxeter

/-!
# A166324

Number of reduced words of length n in Coxeter group on 49 generators S_i with relations (S_i)^2 = (S_i S_j)^10 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=49` `r=10`. The rational generating function is ` (t^10 + 2t^{9}+…+1) / (1128·t^10 - 47·(t^{9}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A166324

/-- Number of generators `g` of `A166324`. -/
abbrev gParam : Nat := 49

/-- Edge label `r` of `A166324`. -/
abbrev rParam : Nat := 10

/-- `C(g-1,2)` for `A166324`. -/
abbrev c1Param : Nat := 1128

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 14

/-- Index type of `A166324` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A166324`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A166324

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A166324 : A166324.argType → A166324.retType := fun n =>
  OEISLib.Coxeter.coxSeq A166324.gParam A166324.rParam n

namespace A166324

/-- Relation that defines `A166324`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A166324 n) := rfl

/-- `A166324` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A166324

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A166324 n := rfl

/-- `A166324` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A166324 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A166324 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A166324
