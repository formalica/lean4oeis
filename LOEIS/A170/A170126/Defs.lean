import OEISLib.Coxeter

/-!
# A170126

Number of reduced words of length n in Coxeter group on 21 generators S_i with relations (S_i)^2 = (S_i S_j)^38 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=21` `r=38`. The rational generating function is ` (t^38 + 2t^{37}+…+1) / (190·t^38 - 19·(t^{37}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A170126

/-- Number of generators `g` of `A170126`. -/
abbrev gParam : Nat := 21

/-- Edge label `r` of `A170126`. -/
abbrev rParam : Nat := 38

/-- `C(g-1,2)` for `A170126`. -/
abbrev c1Param : Nat := 190

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A170126` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A170126`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A170126

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A170126 : A170126.argType → A170126.retType := fun n =>
  OEISLib.Coxeter.coxSeq A170126.gParam A170126.rParam n

namespace A170126

/-- Relation that defines `A170126`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A170126 n) := rfl

/-- `A170126` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A170126

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A170126 n := rfl

/-- `A170126` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A170126 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A170126 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A170126
