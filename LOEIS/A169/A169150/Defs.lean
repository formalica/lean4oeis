import OEISLib.Coxeter

/-!
# A169150

Number of reduced words of length n in Coxeter group on 41 generators S_i with relations (S_i)^2 = (S_i S_j)^26 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=41` `r=26`. The rational generating function is ` (t^26 + 2t^{25}+…+1) / (780·t^26 - 39·(t^{25}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A169150

/-- Number of generators `g` of `A169150`. -/
abbrev gParam : Nat := 41

/-- Edge label `r` of `A169150`. -/
abbrev rParam : Nat := 26

/-- `C(g-1,2)` for `A169150`. -/
abbrev c1Param : Nat := 780

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 14

/-- Index type of `A169150` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A169150`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A169150

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A169150 : A169150.argType → A169150.retType := fun n =>
  OEISLib.Coxeter.coxSeq A169150.gParam A169150.rParam n

namespace A169150

/-- Relation that defines `A169150`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A169150 n) := rfl

/-- `A169150` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A169150

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A169150 n := rfl

/-- `A169150` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A169150 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A169150 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A169150
