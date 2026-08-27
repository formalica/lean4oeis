import OEISLib.Coxeter

/-!
# A169500

Number of reduced words of length n in Coxeter group on 7 generators S_i with relations (S_i)^2 = (S_i S_j)^34 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=7` `r=34`. The rational generating function is ` (t^34 + 2t^{33}+…+1) / (15·t^34 - 5·(t^{33}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A169500

/-- Number of generators `g` of `A169500`. -/
abbrev gParam : Nat := 7

/-- Edge label `r` of `A169500`. -/
abbrev rParam : Nat := 34

/-- `C(g-1,2)` for `A169500`. -/
abbrev c1Param : Nat := 15

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 20

/-- Index type of `A169500` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A169500`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A169500

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A169500 : A169500.argType → A169500.retType := fun n =>
  OEISLib.Coxeter.coxSeq A169500.gParam A169500.rParam n

namespace A169500

/-- Relation that defines `A169500`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A169500 n) := rfl

/-- `A169500` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A169500

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A169500 n := rfl

/-- `A169500` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A169500 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A169500 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A169500
