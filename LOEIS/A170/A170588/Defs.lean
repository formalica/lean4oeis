import OEISLib.Coxeter

/-!
# A170588

Number of reduced words of length n in Coxeter group on 3 generators S_i with relations (S_i)^2 = (S_i S_j)^48 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=3` `r=48`. The rational generating function is ` (t^48 + 2t^{47}+…+1) / (1·t^48 - 1·(t^{47}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A170588

/-- Number of generators `g` of `A170588`. -/
abbrev gParam : Nat := 3

/-- Edge label `r` of `A170588`. -/
abbrev rParam : Nat := 48

/-- `C(g-1,2)` for `A170588`. -/
abbrev c1Param : Nat := 1

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 31

/-- Index type of `A170588` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A170588`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A170588

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A170588 : A170588.argType → A170588.retType := fun n =>
  OEISLib.Coxeter.coxSeq A170588.gParam A170588.rParam n

namespace A170588

/-- Relation that defines `A170588`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A170588 n) := rfl

/-- `A170588` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A170588

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A170588 n := rfl

/-- `A170588` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A170588 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A170588 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A170588
