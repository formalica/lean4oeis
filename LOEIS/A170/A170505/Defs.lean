import OEISLib.Coxeter

/-!
# A170505

Number of reduced words of length n in Coxeter group on 16 generators S_i with relations (S_i)^2 = (S_i S_j)^46 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=16` `r=46`. The rational generating function is ` (t^46 + 2t^{45}+…+1) / (105·t^46 - 14·(t^{45}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A170505

/-- Number of generators `g` of `A170505`. -/
abbrev gParam : Nat := 16

/-- Edge label `r` of `A170505`. -/
abbrev rParam : Nat := 46

/-- `C(g-1,2)` for `A170505`. -/
abbrev c1Param : Nat := 105

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 16

/-- Index type of `A170505` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A170505`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A170505

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A170505 : A170505.argType → A170505.retType := fun n =>
  OEISLib.Coxeter.coxSeq A170505.gParam A170505.rParam n

namespace A170505

/-- Relation that defines `A170505`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A170505 n) := rfl

/-- `A170505` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A170505

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A170505 n := rfl

/-- `A170505` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A170505 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A170505 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A170505
