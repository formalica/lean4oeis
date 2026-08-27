import OEISLib.Coxeter

/-!
# A170498

Number of reduced words of length n in Coxeter group on 9 generators S_i with relations (S_i)^2 = (S_i S_j)^46 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=9` `r=46`. The rational generating function is ` (t^46 + 2t^{45}+…+1) / (28·t^46 - 7·(t^{45}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A170498

/-- Number of generators `g` of `A170498`. -/
abbrev gParam : Nat := 9

/-- Edge label `r` of `A170498`. -/
abbrev rParam : Nat := 46

/-- `C(g-1,2)` for `A170498`. -/
abbrev c1Param : Nat := 28

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 19

/-- Index type of `A170498` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A170498`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A170498

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A170498 : A170498.argType → A170498.retType := fun n =>
  OEISLib.Coxeter.coxSeq A170498.gParam A170498.rParam n

namespace A170498

/-- Relation that defines `A170498`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A170498 n) := rfl

/-- `A170498` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A170498

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A170498 n := rfl

/-- `A170498` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A170498 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A170498 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A170498
