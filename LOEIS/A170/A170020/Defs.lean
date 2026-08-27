import OEISLib.Coxeter

/-!
# A170020

Number of reduced words of length n in Coxeter group on 11 generators S_i with relations (S_i)^2 = (S_i S_j)^36 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=11` `r=36`. The rational generating function is ` (t^36 + 2t^{35}+…+1) / (45·t^36 - 9·(t^{35}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A170020

/-- Number of generators `g` of `A170020`. -/
abbrev gParam : Nat := 11

/-- Edge label `r` of `A170020`. -/
abbrev rParam : Nat := 36

/-- `C(g-1,2)` for `A170020`. -/
abbrev c1Param : Nat := 45

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 17

/-- Index type of `A170020` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A170020`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A170020

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A170020 : A170020.argType → A170020.retType := fun n =>
  OEISLib.Coxeter.coxSeq A170020.gParam A170020.rParam n

namespace A170020

/-- Relation that defines `A170020`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A170020 n) := rfl

/-- `A170020` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A170020

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A170020 n := rfl

/-- `A170020` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A170020 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A170020 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A170020
