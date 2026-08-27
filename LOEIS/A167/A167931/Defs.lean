import OEISLib.Coxeter

/-!
# A167931

Number of reduced words of length n in Coxeter group on 20 generators S_i with relations (S_i)^2 = (S_i S_j)^16 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=20` `r=16`. The rational generating function is ` (t^16 + 2t^{15}+…+1) / (171·t^16 - 18·(t^{15}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A167931

/-- Number of generators `g` of `A167931`. -/
abbrev gParam : Nat := 20

/-- Edge label `r` of `A167931`. -/
abbrev rParam : Nat := 16

/-- `C(g-1,2)` for `A167931`. -/
abbrev c1Param : Nat := 171

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A167931` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A167931`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A167931

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A167931 : A167931.argType → A167931.retType := fun n =>
  OEISLib.Coxeter.coxSeq A167931.gParam A167931.rParam n

namespace A167931

/-- Relation that defines `A167931`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A167931 n) := rfl

/-- `A167931` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A167931

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A167931 n := rfl

/-- `A167931` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A167931 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A167931 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A167931
