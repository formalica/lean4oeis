import OEISLib.Coxeter

/-!
# A170253

Number of reduced words of length n in Coxeter group on 4 generators S_i with relations (S_i)^2 = (S_i S_j)^41 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=4` `r=41`. The rational generating function is ` (t^41 + 2t^{40}+…+1) / (3·t^41 - 2·(t^{40}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A170253

/-- Number of generators `g` of `A170253`. -/
abbrev gParam : Nat := 4

/-- Edge label `r` of `A170253`. -/
abbrev rParam : Nat := 41

/-- `C(g-1,2)` for `A170253`. -/
abbrev c1Param : Nat := 3

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 25

/-- Index type of `A170253` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A170253`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A170253

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A170253 : A170253.argType → A170253.retType := fun n =>
  OEISLib.Coxeter.coxSeq A170253.gParam A170253.rParam n

namespace A170253

/-- Relation that defines `A170253`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A170253 n) := rfl

/-- `A170253` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A170253

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A170253 n := rfl

/-- `A170253` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A170253 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A170253 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A170253
