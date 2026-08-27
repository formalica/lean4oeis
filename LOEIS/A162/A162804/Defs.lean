import OEISLib.Coxeter

/-!
# A162804

Number of reduced words of length n in Coxeter group on 18 generators S_i with relations (S_i)^2 = (S_i S_j)^3 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=18` `r=3`. The rational generating function is ` (t^3 + 2t^{2}+…+1) / (136·t^3 - 16·(t^{2}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A162804

/-- Number of generators `g` of `A162804`. -/
abbrev gParam : Nat := 18

/-- Edge label `r` of `A162804`. -/
abbrev rParam : Nat := 3

/-- `C(g-1,2)` for `A162804`. -/
abbrev c1Param : Nat := 136

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 16

/-- Index type of `A162804` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A162804`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A162804

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A162804 : A162804.argType → A162804.retType := fun n =>
  OEISLib.Coxeter.coxSeq A162804.gParam A162804.rParam n

namespace A162804

/-- Relation that defines `A162804`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A162804 n) := rfl

/-- `A162804` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A162804

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A162804 n := rfl

/-- `A162804` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A162804 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A162804 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A162804
