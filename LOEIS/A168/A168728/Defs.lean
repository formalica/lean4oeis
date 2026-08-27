import OEISLib.Coxeter

/-!
# A168728

Number of reduced words of length n in Coxeter group on 3 generators S_i with relations (S_i)^2 = (S_i S_j)^18 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=3` `r=18`. The rational generating function is ` (t^18 + 2t^{17}+…+1) / (1·t^18 - 1·(t^{17}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A168728

/-- Number of generators `g` of `A168728`. -/
abbrev gParam : Nat := 3

/-- Edge label `r` of `A168728`. -/
abbrev rParam : Nat := 18

/-- `C(g-1,2)` for `A168728`. -/
abbrev c1Param : Nat := 1

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 31

/-- Index type of `A168728` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A168728`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A168728

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A168728 : A168728.argType → A168728.retType := fun n =>
  OEISLib.Coxeter.coxSeq A168728.gParam A168728.rParam n

namespace A168728

/-- Relation that defines `A168728`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A168728 n) := rfl

/-- `A168728` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A168728

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A168728 n := rfl

/-- `A168728` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A168728 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A168728 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A168728
