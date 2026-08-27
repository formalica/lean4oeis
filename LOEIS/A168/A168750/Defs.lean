import OEISLib.Coxeter

/-!
# A168750

Number of reduced words of length n in Coxeter group on 25 generators S_i with relations (S_i)^2 = (S_i S_j)^18 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=25` `r=18`. The rational generating function is ` (t^18 + 2t^{17}+…+1) / (276·t^18 - 23·(t^{17}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A168750

/-- Number of generators `g` of `A168750`. -/
abbrev gParam : Nat := 25

/-- Edge label `r` of `A168750`. -/
abbrev rParam : Nat := 18

/-- `C(g-1,2)` for `A168750`. -/
abbrev c1Param : Nat := 276

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A168750` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A168750`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A168750

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A168750 : A168750.argType → A168750.retType := fun n =>
  OEISLib.Coxeter.coxSeq A168750.gParam A168750.rParam n

namespace A168750

/-- Relation that defines `A168750`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A168750 n) := rfl

/-- `A168750` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A168750

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A168750 n := rfl

/-- `A168750` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A168750 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A168750 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A168750
