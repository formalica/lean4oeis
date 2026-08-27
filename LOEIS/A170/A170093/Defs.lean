import OEISLib.Coxeter

/-!
# A170093

Number of reduced words of length n in Coxeter group on 36 generators S_i with relations (S_i)^2 = (S_i S_j)^37 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=36` `r=37`. The rational generating function is ` (t^37 + 2t^{36}+…+1) / (595·t^37 - 34·(t^{36}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A170093

/-- Number of generators `g` of `A170093`. -/
abbrev gParam : Nat := 36

/-- Edge label `r` of `A170093`. -/
abbrev rParam : Nat := 37

/-- `C(g-1,2)` for `A170093`. -/
abbrev c1Param : Nat := 595

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A170093` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A170093`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A170093

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A170093 : A170093.argType → A170093.retType := fun n =>
  OEISLib.Coxeter.coxSeq A170093.gParam A170093.rParam n

namespace A170093

/-- Relation that defines `A170093`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A170093 n) := rfl

/-- `A170093` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A170093

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A170093 n := rfl

/-- `A170093` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A170093 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A170093 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A170093
