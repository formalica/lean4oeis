import OEISLib.Coxeter

/-!
# A168811

Number of reduced words of length n in Coxeter group on 38 generators S_i with relations (S_i)^2 = (S_i S_j)^19 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=38` `r=19`. The rational generating function is ` (t^19 + 2t^{18}+…+1) / (666·t^19 - 36·(t^{18}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A168811

/-- Number of generators `g` of `A168811`. -/
abbrev gParam : Nat := 38

/-- Edge label `r` of `A168811`. -/
abbrev rParam : Nat := 19

/-- `C(g-1,2)` for `A168811`. -/
abbrev c1Param : Nat := 666

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 14

/-- Index type of `A168811` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A168811`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A168811

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A168811 : A168811.argType → A168811.retType := fun n =>
  OEISLib.Coxeter.coxSeq A168811.gParam A168811.rParam n

namespace A168811

/-- Relation that defines `A168811`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A168811 n) := rfl

/-- `A168811` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A168811

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A168811 n := rfl

/-- `A168811` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A168811 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A168811 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A168811
