import OEISLib.Coxeter

/-!
# A166679

Number of reduced words of length n in Coxeter group on 33 generators S_i with relations (S_i)^2 = (S_i S_j)^12 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=33` `r=12`. The rational generating function is ` (t^12 + 2t^{11}+…+1) / (496·t^12 - 31·(t^{11}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A166679

/-- Number of generators `g` of `A166679`. -/
abbrev gParam : Nat := 33

/-- Edge label `r` of `A166679`. -/
abbrev rParam : Nat := 12

/-- `C(g-1,2)` for `A166679`. -/
abbrev c1Param : Nat := 496

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A166679` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A166679`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A166679

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A166679 : A166679.argType → A166679.retType := fun n =>
  OEISLib.Coxeter.coxSeq A166679.gParam A166679.rParam n

namespace A166679

/-- Relation that defines `A166679`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A166679 n) := rfl

/-- `A166679` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A166679

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A166679 n := rfl

/-- `A166679` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A166679 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A166679 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A166679
