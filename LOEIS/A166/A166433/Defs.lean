import OEISLib.Coxeter

/-!
# A166433

Number of reduced words of length n in Coxeter group on 39 generators S_i with relations (S_i)^2 = (S_i S_j)^11 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=39` `r=11`. The rational generating function is ` (t^11 + 2t^{10}+…+1) / (703·t^11 - 37·(t^{10}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A166433

/-- Number of generators `g` of `A166433`. -/
abbrev gParam : Nat := 39

/-- Edge label `r` of `A166433`. -/
abbrev rParam : Nat := 11

/-- `C(g-1,2)` for `A166433`. -/
abbrev c1Param : Nat := 703

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 14

/-- Index type of `A166433` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A166433`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A166433

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A166433 : A166433.argType → A166433.retType := fun n =>
  OEISLib.Coxeter.coxSeq A166433.gParam A166433.rParam n

namespace A166433

/-- Relation that defines `A166433`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A166433 n) := rfl

/-- `A166433` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A166433

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A166433 n := rfl

/-- `A166433` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A166433 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A166433 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A166433
