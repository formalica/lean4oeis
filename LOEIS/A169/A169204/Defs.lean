import OEISLib.Coxeter

/-!
# A169204

Number of reduced words of length n in Coxeter group on 47 generators S_i with relations (S_i)^2 = (S_i S_j)^27 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=47` `r=27`. The rational generating function is ` (t^27 + 2t^{26}+…+1) / (1035·t^27 - 45·(t^{26}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A169204

/-- Number of generators `g` of `A169204`. -/
abbrev gParam : Nat := 47

/-- Edge label `r` of `A169204`. -/
abbrev rParam : Nat := 27

/-- `C(g-1,2)` for `A169204`. -/
abbrev c1Param : Nat := 1035

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 14

/-- Index type of `A169204` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A169204`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A169204

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A169204 : A169204.argType → A169204.retType := fun n =>
  OEISLib.Coxeter.coxSeq A169204.gParam A169204.rParam n

namespace A169204

/-- Relation that defines `A169204`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A169204 n) := rfl

/-- `A169204` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A169204

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A169204 n := rfl

/-- `A169204` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A169204 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A169204 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A169204
