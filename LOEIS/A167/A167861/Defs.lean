import OEISLib.Coxeter

/-!
# A167861

Number of reduced words of length n in Coxeter group on 46 generators S_i with relations (S_i)^2 = (S_i S_j)^15 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=46` `r=15`. The rational generating function is ` (t^15 + 2t^{14}+…+1) / (990·t^15 - 44·(t^{14}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A167861

/-- Number of generators `g` of `A167861`. -/
abbrev gParam : Nat := 46

/-- Edge label `r` of `A167861`. -/
abbrev rParam : Nat := 15

/-- `C(g-1,2)` for `A167861`. -/
abbrev c1Param : Nat := 990

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 14

/-- Index type of `A167861` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A167861`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A167861

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A167861 : A167861.argType → A167861.retType := fun n =>
  OEISLib.Coxeter.coxSeq A167861.gParam A167861.rParam n

namespace A167861

/-- Relation that defines `A167861`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A167861 n) := rfl

/-- `A167861` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A167861

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A167861 n := rfl

/-- `A167861` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A167861 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A167861 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A167861
