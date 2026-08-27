import OEISLib.Coxeter

/-!
# A170675

Number of reduced words of length n in Coxeter group on 42 generators S_i with relations (S_i)^2 = (S_i S_j)^49 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=42` `r=49`. The rational generating function is ` (t^49 + 2t^{48}+…+1) / (820·t^49 - 40·(t^{48}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A170675

/-- Number of generators `g` of `A170675`. -/
abbrev gParam : Nat := 42

/-- Edge label `r` of `A170675`. -/
abbrev rParam : Nat := 49

/-- `C(g-1,2)` for `A170675`. -/
abbrev c1Param : Nat := 820

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 14

/-- Index type of `A170675` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A170675`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A170675

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A170675 : A170675.argType → A170675.retType := fun n =>
  OEISLib.Coxeter.coxSeq A170675.gParam A170675.rParam n

namespace A170675

/-- Relation that defines `A170675`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A170675 n) := rfl

/-- `A170675` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A170675

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A170675 n := rfl

/-- `A170675` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A170675 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A170675 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A170675
