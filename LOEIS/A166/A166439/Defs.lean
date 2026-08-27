import OEISLib.Coxeter

/-!
# A166439

Number of reduced words of length n in Coxeter group on 45 generators S_i with relations (S_i)^2 = (S_i S_j)^11 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=45` `r=11`. The rational generating function is ` (t^11 + 2t^{10}+…+1) / (946·t^11 - 43·(t^{10}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A166439

/-- Number of generators `g` of `A166439`. -/
abbrev gParam : Nat := 45

/-- Edge label `r` of `A166439`. -/
abbrev rParam : Nat := 11

/-- `C(g-1,2)` for `A166439`. -/
abbrev c1Param : Nat := 946

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 14

/-- Index type of `A166439` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A166439`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A166439

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A166439 : A166439.argType → A166439.retType := fun n =>
  OEISLib.Coxeter.coxSeq A166439.gParam A166439.rParam n

namespace A166439

/-- Relation that defines `A166439`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A166439 n) := rfl

/-- `A166439` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A166439

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A166439 n := rfl

/-- `A166439` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A166439 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A166439 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A166439
