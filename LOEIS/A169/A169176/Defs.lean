import OEISLib.Coxeter

/-!
# A169176

Number of reduced words of length n in Coxeter group on 19 generators S_i with relations (S_i)^2 = (S_i S_j)^27 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=19` `r=27`. The rational generating function is ` (t^27 + 2t^{26}+…+1) / (153·t^27 - 17·(t^{26}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A169176

/-- Number of generators `g` of `A169176`. -/
abbrev gParam : Nat := 19

/-- Edge label `r` of `A169176`. -/
abbrev rParam : Nat := 27

/-- `C(g-1,2)` for `A169176`. -/
abbrev c1Param : Nat := 153

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A169176` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A169176`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A169176

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A169176 : A169176.argType → A169176.retType := fun n =>
  OEISLib.Coxeter.coxSeq A169176.gParam A169176.rParam n

namespace A169176

/-- Relation that defines `A169176`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A169176 n) := rfl

/-- `A169176` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A169176

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A169176 n := rfl

/-- `A169176` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A169176 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A169176 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A169176
