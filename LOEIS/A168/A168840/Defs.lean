import OEISLib.Coxeter

/-!
# A168840

Number of reduced words of length n in Coxeter group on 19 generators S_i with relations (S_i)^2 = (S_i S_j)^20 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=19` `r=20`. The rational generating function is ` (t^20 + 2t^{19}+…+1) / (153·t^20 - 17·(t^{19}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A168840

/-- Number of generators `g` of `A168840`. -/
abbrev gParam : Nat := 19

/-- Edge label `r` of `A168840`. -/
abbrev rParam : Nat := 20

/-- `C(g-1,2)` for `A168840`. -/
abbrev c1Param : Nat := 153

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A168840` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A168840`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A168840

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A168840 : A168840.argType → A168840.retType := fun n =>
  OEISLib.Coxeter.coxSeq A168840.gParam A168840.rParam n

namespace A168840

/-- Relation that defines `A168840`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A168840 n) := rfl

/-- `A168840` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A168840

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A168840 n := rfl

/-- `A168840` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A168840 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A168840 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A168840
