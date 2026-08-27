import OEISLib.Coxeter

/-!
# A166971

Number of reduced words of length n in Coxeter group on 15 generators S_i with relations (S_i)^2 = (S_i S_j)^13 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=15` `r=13`. The rational generating function is ` (t^13 + 2t^{12}+…+1) / (91·t^13 - 13·(t^{12}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A166971

/-- Number of generators `g` of `A166971`. -/
abbrev gParam : Nat := 15

/-- Edge label `r` of `A166971`. -/
abbrev rParam : Nat := 13

/-- `C(g-1,2)` for `A166971`. -/
abbrev c1Param : Nat := 91

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 16

/-- Index type of `A166971` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A166971`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A166971

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A166971 : A166971.argType → A166971.retType := fun n =>
  OEISLib.Coxeter.coxSeq A166971.gParam A166971.rParam n

namespace A166971

/-- Relation that defines `A166971`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A166971 n) := rfl

/-- `A166971` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A166971

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A166971 n := rfl

/-- `A166971` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A166971 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A166971 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A166971
