import OEISLib.Coxeter

/-!
# A166411

Number of reduced words of length n in Coxeter group on 17 generators S_i with relations (S_i)^2 = (S_i S_j)^11 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=17` `r=11`. The rational generating function is ` (t^11 + 2t^{10}+…+1) / (120·t^11 - 15·(t^{10}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A166411

/-- Number of generators `g` of `A166411`. -/
abbrev gParam : Nat := 17

/-- Edge label `r` of `A166411`. -/
abbrev rParam : Nat := 11

/-- `C(g-1,2)` for `A166411`. -/
abbrev c1Param : Nat := 120

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 16

/-- Index type of `A166411` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A166411`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A166411

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A166411 : A166411.argType → A166411.retType := fun n =>
  OEISLib.Coxeter.coxSeq A166411.gParam A166411.rParam n

namespace A166411

/-- Relation that defines `A166411`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A166411 n) := rfl

/-- `A166411` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A166411

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A166411 n := rfl

/-- `A166411` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A166411 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A166411 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A166411
