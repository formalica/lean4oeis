import OEISLib.Coxeter

/-!
# A166130

Number of reduced words of length n in Coxeter group on 34 generators S_i with relations (S_i)^2 = (S_i S_j)^10 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=34` `r=10`. The rational generating function is ` (t^10 + 2t^{9}+…+1) / (528·t^10 - 32·(t^{9}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A166130

/-- Number of generators `g` of `A166130`. -/
abbrev gParam : Nat := 34

/-- Edge label `r` of `A166130`. -/
abbrev rParam : Nat := 10

/-- `C(g-1,2)` for `A166130`. -/
abbrev c1Param : Nat := 528

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A166130` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A166130`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A166130

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A166130 : A166130.argType → A166130.retType := fun n =>
  OEISLib.Coxeter.coxSeq A166130.gParam A166130.rParam n

namespace A166130

/-- Relation that defines `A166130`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A166130 n) := rfl

/-- `A166130` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A166130

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A166130 n := rfl

/-- `A166130` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A166130 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A166130 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A166130
