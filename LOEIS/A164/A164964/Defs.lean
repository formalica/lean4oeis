import OEISLib.Coxeter

/-!
# A164964

Number of reduced words of length n in Coxeter group on 26 generators S_i with relations (S_i)^2 = (S_i S_j)^8 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=26` `r=8`. The rational generating function is ` (t^8 + 2t^{7}+…+1) / (300·t^8 - 24·(t^{7}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A164964

/-- Number of generators `g` of `A164964`. -/
abbrev gParam : Nat := 26

/-- Edge label `r` of `A164964`. -/
abbrev rParam : Nat := 8

/-- `C(g-1,2)` for `A164964`. -/
abbrev c1Param : Nat := 300

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A164964` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A164964`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A164964

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A164964 : A164964.argType → A164964.retType := fun n =>
  OEISLib.Coxeter.coxSeq A164964.gParam A164964.rParam n

namespace A164964

/-- Relation that defines `A164964`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A164964 n) := rfl

/-- `A164964` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A164964

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A164964 n := rfl

/-- `A164964` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A164964 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A164964 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A164964
