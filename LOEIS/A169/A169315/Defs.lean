import OEISLib.Coxeter

/-!
# A169315

Number of reduced words of length n in Coxeter group on 14 generators S_i with relations (S_i)^2 = (S_i S_j)^30 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=14` `r=30`. The rational generating function is ` (t^30 + 2t^{29}+…+1) / (78·t^30 - 12·(t^{29}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A169315

/-- Number of generators `g` of `A169315`. -/
abbrev gParam : Nat := 14

/-- Edge label `r` of `A169315`. -/
abbrev rParam : Nat := 30

/-- `C(g-1,2)` for `A169315`. -/
abbrev c1Param : Nat := 78

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 16

/-- Index type of `A169315` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A169315`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A169315

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A169315 : A169315.argType → A169315.retType := fun n =>
  OEISLib.Coxeter.coxSeq A169315.gParam A169315.rParam n

namespace A169315

/-- Relation that defines `A169315`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A169315 n) := rfl

/-- `A169315` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A169315

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A169315 n := rfl

/-- `A169315` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A169315 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A169315 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A169315
