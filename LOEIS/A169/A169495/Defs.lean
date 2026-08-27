import OEISLib.Coxeter

/-!
# A169495

Number of reduced words of length n in Coxeter group on 50 generators S_i with relations (S_i)^2 = (S_i S_j)^33 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=50` `r=33`. The rational generating function is ` (t^33 + 2t^{32}+…+1) / (1176·t^33 - 48·(t^{32}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A169495

/-- Number of generators `g` of `A169495`. -/
abbrev gParam : Nat := 50

/-- Edge label `r` of `A169495`. -/
abbrev rParam : Nat := 33

/-- `C(g-1,2)` for `A169495`. -/
abbrev c1Param : Nat := 1176

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 14

/-- Index type of `A169495` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A169495`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A169495

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A169495 : A169495.argType → A169495.retType := fun n =>
  OEISLib.Coxeter.coxSeq A169495.gParam A169495.rParam n

namespace A169495

/-- Relation that defines `A169495`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A169495 n) := rfl

/-- `A169495` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A169495

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A169495 n := rfl

/-- `A169495` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A169495 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A169495 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A169495
