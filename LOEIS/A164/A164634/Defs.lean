import OEISLib.Coxeter

/-!
# A164634

Number of reduced words of length n in Coxeter group on 21 generators S_i with relations (S_i)^2 = (S_i S_j)^7 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=21` `r=7`. The rational generating function is ` (t^7 + 2t^{6}+…+1) / (190·t^7 - 19·(t^{6}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A164634

/-- Number of generators `g` of `A164634`. -/
abbrev gParam : Nat := 21

/-- Edge label `r` of `A164634`. -/
abbrev rParam : Nat := 7

/-- `C(g-1,2)` for `A164634`. -/
abbrev c1Param : Nat := 190

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A164634` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A164634`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A164634

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A164634 : A164634.argType → A164634.retType := fun n =>
  OEISLib.Coxeter.coxSeq A164634.gParam A164634.rParam n

namespace A164634

/-- Relation that defines `A164634`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A164634 n) := rfl

/-- `A164634` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A164634

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A164634 n := rfl

/-- `A164634` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A164634 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A164634 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A164634
