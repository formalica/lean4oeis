import OEISLib.Coxeter

/-!
# A163923

Number of reduced words of length n in Coxeter group on 7 generators S_i with relations (S_i)^2 = (S_i S_j)^6 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=7` `r=6`. The rational generating function is ` (t^6 + 2t^{5}+…+1) / (15·t^6 - 5·(t^{5}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A163923

/-- Number of generators `g` of `A163923`. -/
abbrev gParam : Nat := 7

/-- Edge label `r` of `A163923`. -/
abbrev rParam : Nat := 6

/-- `C(g-1,2)` for `A163923`. -/
abbrev c1Param : Nat := 15

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 20

/-- Index type of `A163923` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A163923`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A163923

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A163923 : A163923.argType → A163923.retType := fun n =>
  OEISLib.Coxeter.coxSeq A163923.gParam A163923.rParam n

namespace A163923

/-- Relation that defines `A163923`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A163923 n) := rfl

/-- `A163923` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A163923

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A163923 n := rfl

/-- `A163923` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A163923 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A163923 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A163923
