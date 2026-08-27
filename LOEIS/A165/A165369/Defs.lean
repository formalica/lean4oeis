import OEISLib.Coxeter

/-!
# A165369

Number of reduced words of length n in Coxeter group on 26 generators S_i with relations (S_i)^2 = (S_i S_j)^9 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=26` `r=9`. The rational generating function is ` (t^9 + 2t^{8}+…+1) / (300·t^9 - 24·(t^{8}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A165369

/-- Number of generators `g` of `A165369`. -/
abbrev gParam : Nat := 26

/-- Edge label `r` of `A165369`. -/
abbrev rParam : Nat := 9

/-- `C(g-1,2)` for `A165369`. -/
abbrev c1Param : Nat := 300

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A165369` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A165369`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A165369

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A165369 : A165369.argType → A165369.retType := fun n =>
  OEISLib.Coxeter.coxSeq A165369.gParam A165369.rParam n

namespace A165369

/-- Relation that defines `A165369`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A165369 n) := rfl

/-- `A165369` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A165369

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A165369 n := rfl

/-- `A165369` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A165369 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A165369 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A165369
