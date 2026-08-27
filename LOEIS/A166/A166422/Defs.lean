import OEISLib.Coxeter

/-!
# A166422

Number of reduced words of length n in Coxeter group on 28 generators S_i with relations (S_i)^2 = (S_i S_j)^11 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=28` `r=11`. The rational generating function is ` (t^11 + 2t^{10}+…+1) / (351·t^11 - 26·(t^{10}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A166422

/-- Number of generators `g` of `A166422`. -/
abbrev gParam : Nat := 28

/-- Edge label `r` of `A166422`. -/
abbrev rParam : Nat := 11

/-- `C(g-1,2)` for `A166422`. -/
abbrev c1Param : Nat := 351

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A166422` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A166422`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A166422

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A166422 : A166422.argType → A166422.retType := fun n =>
  OEISLib.Coxeter.coxSeq A166422.gParam A166422.rParam n

namespace A166422

/-- Relation that defines `A166422`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A166422 n) := rfl

/-- `A166422` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A166422

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A166422 n := rfl

/-- `A166422` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A166422 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A166422 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A166422
