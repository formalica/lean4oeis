import OEISLib.Coxeter

/-!
# A162983

Number of reduced words of length n in Coxeter group on 10 generators S_i with relations (S_i)^2 = (S_i S_j)^4 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=10` `r=4`. The rational generating function is ` (t^4 + 2t^{3}+…+1) / (36·t^4 - 8·(t^{3}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A162983

/-- Number of generators `g` of `A162983`. -/
abbrev gParam : Nat := 10

/-- Edge label `r` of `A162983`. -/
abbrev rParam : Nat := 4

/-- `C(g-1,2)` for `A162983`. -/
abbrev c1Param : Nat := 36

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 18

/-- Index type of `A162983` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A162983`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A162983

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A162983 : A162983.argType → A162983.retType := fun n =>
  OEISLib.Coxeter.coxSeq A162983.gParam A162983.rParam n

namespace A162983

/-- Relation that defines `A162983`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A162983 n) := rfl

/-- `A162983` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A162983

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A162983 n := rfl

/-- `A162983` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A162983 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A162983 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A162983
