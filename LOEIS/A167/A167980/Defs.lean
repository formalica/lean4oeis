import OEISLib.Coxeter

/-!
# A167980

Number of reduced words of length n in Coxeter group on 48 generators S_i with relations (S_i)^2 = (S_i S_j)^16 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=48` `r=16`. The rational generating function is ` (t^16 + 2t^{15}+…+1) / (1081·t^16 - 46·(t^{15}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A167980

/-- Number of generators `g` of `A167980`. -/
abbrev gParam : Nat := 48

/-- Edge label `r` of `A167980`. -/
abbrev rParam : Nat := 16

/-- `C(g-1,2)` for `A167980`. -/
abbrev c1Param : Nat := 1081

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 14

/-- Index type of `A167980` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A167980`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A167980

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A167980 : A167980.argType → A167980.retType := fun n =>
  OEISLib.Coxeter.coxSeq A167980.gParam A167980.rParam n

namespace A167980

/-- Relation that defines `A167980`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A167980 n) := rfl

/-- `A167980` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A167980

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A167980 n := rfl

/-- `A167980` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A167980 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A167980 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A167980
