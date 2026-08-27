import OEISLib.Coxeter

/-!
# A169571

Number of reduced words of length n in Coxeter group on 30 generators S_i with relations (S_i)^2 = (S_i S_j)^35 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=30` `r=35`. The rational generating function is ` (t^35 + 2t^{34}+…+1) / (406·t^35 - 28·(t^{34}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A169571

/-- Number of generators `g` of `A169571`. -/
abbrev gParam : Nat := 30

/-- Edge label `r` of `A169571`. -/
abbrev rParam : Nat := 35

/-- `C(g-1,2)` for `A169571`. -/
abbrev c1Param : Nat := 406

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A169571` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A169571`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A169571

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A169571 : A169571.argType → A169571.retType := fun n =>
  OEISLib.Coxeter.coxSeq A169571.gParam A169571.rParam n

namespace A169571

/-- Relation that defines `A169571`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A169571 n) := rfl

/-- `A169571` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A169571

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A169571 n := rfl

/-- `A169571` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A169571 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A169571 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A169571
