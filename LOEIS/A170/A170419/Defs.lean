import OEISLib.Coxeter

/-!
# A170419

Number of reduced words of length n in Coxeter group on 26 generators S_i with relations (S_i)^2 = (S_i S_j)^44 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=26` `r=44`. The rational generating function is ` (t^44 + 2t^{43}+…+1) / (300·t^44 - 24·(t^{43}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A170419

/-- Number of generators `g` of `A170419`. -/
abbrev gParam : Nat := 26

/-- Edge label `r` of `A170419`. -/
abbrev rParam : Nat := 44

/-- `C(g-1,2)` for `A170419`. -/
abbrev c1Param : Nat := 300

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A170419` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A170419`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A170419

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A170419 : A170419.argType → A170419.retType := fun n =>
  OEISLib.Coxeter.coxSeq A170419.gParam A170419.rParam n

namespace A170419

/-- Relation that defines `A170419`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A170419 n) := rfl

/-- `A170419` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A170419

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A170419 n := rfl

/-- `A170419` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A170419 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A170419 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A170419
