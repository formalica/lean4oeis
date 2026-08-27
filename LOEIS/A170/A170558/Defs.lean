import OEISLib.Coxeter

/-!
# A170558

Number of reduced words of length n in Coxeter group on 21 generators S_i with relations (S_i)^2 = (S_i S_j)^47 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=21` `r=47`. The rational generating function is ` (t^47 + 2t^{46}+…+1) / (190·t^47 - 19·(t^{46}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A170558

/-- Number of generators `g` of `A170558`. -/
abbrev gParam : Nat := 21

/-- Edge label `r` of `A170558`. -/
abbrev rParam : Nat := 47

/-- `C(g-1,2)` for `A170558`. -/
abbrev c1Param : Nat := 190

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A170558` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A170558`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A170558

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A170558 : A170558.argType → A170558.retType := fun n =>
  OEISLib.Coxeter.coxSeq A170558.gParam A170558.rParam n

namespace A170558

/-- Relation that defines `A170558`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A170558 n) := rfl

/-- `A170558` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A170558

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A170558 n := rfl

/-- `A170558` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A170558 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A170558 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A170558
