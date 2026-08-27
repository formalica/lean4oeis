import OEISLib.Coxeter

/-!
# A167114

Number of reduced words of length n in Coxeter group on 13 generators S_i with relations (S_i)^2 = (S_i S_j)^14 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=13` `r=14`. The rational generating function is ` (t^14 + 2t^{13}+…+1) / (66·t^14 - 11·(t^{13}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A167114

/-- Number of generators `g` of `A167114`. -/
abbrev gParam : Nat := 13

/-- Edge label `r` of `A167114`. -/
abbrev rParam : Nat := 14

/-- `C(g-1,2)` for `A167114`. -/
abbrev c1Param : Nat := 66

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 16

/-- Index type of `A167114` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A167114`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A167114

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A167114 : A167114.argType → A167114.retType := fun n =>
  OEISLib.Coxeter.coxSeq A167114.gParam A167114.rParam n

namespace A167114

/-- Relation that defines `A167114`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A167114 n) := rfl

/-- `A167114` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A167114

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A167114 n := rfl

/-- `A167114` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A167114 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A167114 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A167114
