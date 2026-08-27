import OEISLib.Coxeter

/-!
# A168972

Number of reduced words of length n in Coxeter group on 7 generators S_i with relations (S_i)^2 = (S_i S_j)^23 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=7` `r=23`. The rational generating function is ` (t^23 + 2t^{22}+…+1) / (15·t^23 - 5·(t^{22}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A168972

/-- Number of generators `g` of `A168972`. -/
abbrev gParam : Nat := 7

/-- Edge label `r` of `A168972`. -/
abbrev rParam : Nat := 23

/-- `C(g-1,2)` for `A168972`. -/
abbrev c1Param : Nat := 15

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 20

/-- Index type of `A168972` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A168972`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A168972

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A168972 : A168972.argType → A168972.retType := fun n =>
  OEISLib.Coxeter.coxSeq A168972.gParam A168972.rParam n

namespace A168972

/-- Relation that defines `A168972`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A168972 n) := rfl

/-- `A168972` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A168972

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A168972 n := rfl

/-- `A168972` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A168972 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A168972 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A168972
