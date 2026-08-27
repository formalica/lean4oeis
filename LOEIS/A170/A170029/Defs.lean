import OEISLib.Coxeter

/-!
# A170029

Number of reduced words of length n in Coxeter group on 20 generators S_i with relations (S_i)^2 = (S_i S_j)^36 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=20` `r=36`. The rational generating function is ` (t^36 + 2t^{35}+…+1) / (171·t^36 - 18·(t^{35}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A170029

/-- Number of generators `g` of `A170029`. -/
abbrev gParam : Nat := 20

/-- Edge label `r` of `A170029`. -/
abbrev rParam : Nat := 36

/-- `C(g-1,2)` for `A170029`. -/
abbrev c1Param : Nat := 171

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A170029` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A170029`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A170029

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A170029 : A170029.argType → A170029.retType := fun n =>
  OEISLib.Coxeter.coxSeq A170029.gParam A170029.rParam n

namespace A170029

/-- Relation that defines `A170029`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A170029 n) := rfl

/-- `A170029` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A170029

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A170029 n := rfl

/-- `A170029` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A170029 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A170029 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A170029
