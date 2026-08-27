import OEISLib.Coxeter

/-!
# A167900

Number of reduced words of length n in Coxeter group on 9 generators S_i with relations (S_i)^2 = (S_i S_j)^16 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=9` `r=16`. The rational generating function is ` (t^16 + 2t^{15}+…+1) / (28·t^16 - 7·(t^{15}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A167900

/-- Number of generators `g` of `A167900`. -/
abbrev gParam : Nat := 9

/-- Edge label `r` of `A167900`. -/
abbrev rParam : Nat := 16

/-- `C(g-1,2)` for `A167900`. -/
abbrev c1Param : Nat := 28

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 19

/-- Index type of `A167900` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A167900`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A167900

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A167900 : A167900.argType → A167900.retType := fun n =>
  OEISLib.Coxeter.coxSeq A167900.gParam A167900.rParam n

namespace A167900

/-- Relation that defines `A167900`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A167900 n) := rfl

/-- `A167900` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A167900

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A167900 n := rfl

/-- `A167900` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A167900 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A167900 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A167900
