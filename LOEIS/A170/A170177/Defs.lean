import OEISLib.Coxeter

/-!
# A170177

Number of reduced words of length n in Coxeter group on 24 generators S_i with relations (S_i)^2 = (S_i S_j)^39 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=24` `r=39`. The rational generating function is ` (t^39 + 2t^{38}+…+1) / (253·t^39 - 22·(t^{38}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A170177

/-- Number of generators `g` of `A170177`. -/
abbrev gParam : Nat := 24

/-- Edge label `r` of `A170177`. -/
abbrev rParam : Nat := 39

/-- `C(g-1,2)` for `A170177`. -/
abbrev c1Param : Nat := 253

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A170177` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A170177`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A170177

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A170177 : A170177.argType → A170177.retType := fun n =>
  OEISLib.Coxeter.coxSeq A170177.gParam A170177.rParam n

namespace A170177

/-- Relation that defines `A170177`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A170177 n) := rfl

/-- `A170177` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A170177

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A170177 n := rfl

/-- `A170177` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A170177 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A170177 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A170177
