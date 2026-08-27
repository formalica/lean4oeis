import OEISLib.Coxeter

/-!
# A169457

Number of reduced words of length n in Coxeter group on 12 generators S_i with relations (S_i)^2 = (S_i S_j)^33 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=12` `r=33`. The rational generating function is ` (t^33 + 2t^{32}+…+1) / (55·t^33 - 10·(t^{32}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A169457

/-- Number of generators `g` of `A169457`. -/
abbrev gParam : Nat := 12

/-- Edge label `r` of `A169457`. -/
abbrev rParam : Nat := 33

/-- `C(g-1,2)` for `A169457`. -/
abbrev c1Param : Nat := 55

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 17

/-- Index type of `A169457` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A169457`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A169457

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A169457 : A169457.argType → A169457.retType := fun n =>
  OEISLib.Coxeter.coxSeq A169457.gParam A169457.rParam n

namespace A169457

/-- Relation that defines `A169457`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A169457 n) := rfl

/-- `A169457` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A169457

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A169457 n := rfl

/-- `A169457` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A169457 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A169457 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A169457
