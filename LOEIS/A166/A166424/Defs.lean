import OEISLib.Coxeter

/-!
# A166424

Number of reduced words of length n in Coxeter group on 30 generators S_i with relations (S_i)^2 = (S_i S_j)^11 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=30` `r=11`. The rational generating function is ` (t^11 + 2t^{10}+…+1) / (406·t^11 - 28·(t^{10}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A166424

/-- Number of generators `g` of `A166424`. -/
abbrev gParam : Nat := 30

/-- Edge label `r` of `A166424`. -/
abbrev rParam : Nat := 11

/-- `C(g-1,2)` for `A166424`. -/
abbrev c1Param : Nat := 406

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A166424` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A166424`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A166424

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A166424 : A166424.argType → A166424.retType := fun n =>
  OEISLib.Coxeter.coxSeq A166424.gParam A166424.rParam n

namespace A166424

/-- Relation that defines `A166424`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A166424 n) := rfl

/-- `A166424` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A166424

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A166424 n := rfl

/-- `A166424` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A166424 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A166424 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A166424
