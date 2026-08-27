import OEISLib.Coxeter

/-!
# A169494

Number of reduced words of length n in Coxeter group on 49 generators S_i with relations (S_i)^2 = (S_i S_j)^33 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=49` `r=33`. The rational generating function is ` (t^33 + 2t^{32}+…+1) / (1128·t^33 - 47·(t^{32}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A169494

/-- Number of generators `g` of `A169494`. -/
abbrev gParam : Nat := 49

/-- Edge label `r` of `A169494`. -/
abbrev rParam : Nat := 33

/-- `C(g-1,2)` for `A169494`. -/
abbrev c1Param : Nat := 1128

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 14

/-- Index type of `A169494` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A169494`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A169494

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A169494 : A169494.argType → A169494.retType := fun n =>
  OEISLib.Coxeter.coxSeq A169494.gParam A169494.rParam n

namespace A169494

/-- Relation that defines `A169494`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A169494 n) := rfl

/-- `A169494` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A169494

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A169494 n := rfl

/-- `A169494` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A169494 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A169494 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A169494
