import OEISLib.Coxeter

/-!
# A167173

Number of reduced words of length n in Coxeter group on 22 generators S_i with relations (S_i)^2 = (S_i S_j)^14 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=22` `r=14`. The rational generating function is ` (t^14 + 2t^{13}+…+1) / (210·t^14 - 20·(t^{13}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A167173

/-- Number of generators `g` of `A167173`. -/
abbrev gParam : Nat := 22

/-- Edge label `r` of `A167173`. -/
abbrev rParam : Nat := 14

/-- `C(g-1,2)` for `A167173`. -/
abbrev c1Param : Nat := 210

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A167173` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A167173`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A167173

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A167173 : A167173.argType → A167173.retType := fun n =>
  OEISLib.Coxeter.coxSeq A167173.gParam A167173.rParam n

namespace A167173

/-- Relation that defines `A167173`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A167173 n) := rfl

/-- `A167173` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A167173

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A167173 n := rfl

/-- `A167173` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A167173 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A167173 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A167173
