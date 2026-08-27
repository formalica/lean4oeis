import OEISLib.Coxeter

/-!
# A169392

Number of reduced words of length n in Coxeter group on 43 generators S_i with relations (S_i)^2 = (S_i S_j)^31 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=43` `r=31`. The rational generating function is ` (t^31 + 2t^{30}+…+1) / (861·t^31 - 41·(t^{30}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A169392

/-- Number of generators `g` of `A169392`. -/
abbrev gParam : Nat := 43

/-- Edge label `r` of `A169392`. -/
abbrev rParam : Nat := 31

/-- `C(g-1,2)` for `A169392`. -/
abbrev c1Param : Nat := 861

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 14

/-- Index type of `A169392` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A169392`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A169392

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A169392 : A169392.argType → A169392.retType := fun n =>
  OEISLib.Coxeter.coxSeq A169392.gParam A169392.rParam n

namespace A169392

/-- Relation that defines `A169392`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A169392 n) := rfl

/-- `A169392` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A169392

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A169392 n := rfl

/-- `A169392` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A169392 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A169392 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A169392
