import OEISLib.Coxeter

/-!
# A168931

Number of reduced words of length n in Coxeter group on 14 generators S_i with relations (S_i)^2 = (S_i S_j)^22 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=14` `r=22`. The rational generating function is ` (t^22 + 2t^{21}+…+1) / (78·t^22 - 12·(t^{21}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A168931

/-- Number of generators `g` of `A168931`. -/
abbrev gParam : Nat := 14

/-- Edge label `r` of `A168931`. -/
abbrev rParam : Nat := 22

/-- `C(g-1,2)` for `A168931`. -/
abbrev c1Param : Nat := 78

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 16

/-- Index type of `A168931` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A168931`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A168931

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A168931 : A168931.argType → A168931.retType := fun n =>
  OEISLib.Coxeter.coxSeq A168931.gParam A168931.rParam n

namespace A168931

/-- Relation that defines `A168931`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A168931 n) := rfl

/-- `A168931` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A168931

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A168931 n := rfl

/-- `A168931` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A168931 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A168931 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A168931
