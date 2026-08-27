import OEISLib.Coxeter

/-!
# A169417

Number of reduced words of length n in Coxeter group on 20 generators S_i with relations (S_i)^2 = (S_i S_j)^32 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=20` `r=32`. The rational generating function is ` (t^32 + 2t^{31}+…+1) / (171·t^32 - 18·(t^{31}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A169417

/-- Number of generators `g` of `A169417`. -/
abbrev gParam : Nat := 20

/-- Edge label `r` of `A169417`. -/
abbrev rParam : Nat := 32

/-- `C(g-1,2)` for `A169417`. -/
abbrev c1Param : Nat := 171

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 18

/-- Index type of `A169417` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A169417`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A169417

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A169417 : A169417.argType → A169417.retType := fun n =>
  OEISLib.Coxeter.coxSeq A169417.gParam A169417.rParam n

namespace A169417

/-- Relation that defines `A169417`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A169417 n) := rfl

/-- `A169417` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A169417

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A169417 n := rfl

/-- `A169417` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A169417 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A169417 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A169417
