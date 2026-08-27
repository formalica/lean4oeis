import OEISLib.Coxeter

/-!
# A166910

Number of reduced words of length n in Coxeter group on 8 generators S_i with relations (S_i)^2 = (S_i S_j)^13 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=8` `r=13`. The rational generating function is ` (t^13 + 2t^{12}+…+1) / (21·t^13 - 6·(t^{12}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A166910

/-- Number of generators `g` of `A166910`. -/
abbrev gParam : Nat := 8

/-- Edge label `r` of `A166910`. -/
abbrev rParam : Nat := 13

/-- `C(g-1,2)` for `A166910`. -/
abbrev c1Param : Nat := 21

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 19

/-- Index type of `A166910` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A166910`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A166910

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A166910 : A166910.argType → A166910.retType := fun n =>
  OEISLib.Coxeter.coxSeq A166910.gParam A166910.rParam n

namespace A166910

/-- Relation that defines `A166910`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A166910 n) := rfl

/-- `A166910` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A166910

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A166910 n := rfl

/-- `A166910` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A166910 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A166910 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A166910
