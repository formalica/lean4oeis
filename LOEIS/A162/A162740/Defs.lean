import OEISLib.Coxeter

/-!
# A162740

Number of reduced words of length n in Coxeter group on 4 generators S_i with relations (S_i)^2 = (S_i S_j)^3 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=4` `r=3`. The rational generating function is ` (t^3 + 2t^{2}+…+1) / (3·t^3 - 2·(t^{2}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A162740

/-- Number of generators `g` of `A162740`. -/
abbrev gParam : Nat := 4

/-- Edge label `r` of `A162740`. -/
abbrev rParam : Nat := 3

/-- `C(g-1,2)` for `A162740`. -/
abbrev c1Param : Nat := 3

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 30

/-- Index type of `A162740` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A162740`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A162740

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A162740 : A162740.argType → A162740.retType := fun n =>
  OEISLib.Coxeter.coxSeq A162740.gParam A162740.rParam n

namespace A162740

/-- Relation that defines `A162740`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A162740 n) := rfl

/-- `A162740` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A162740

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A162740 n := rfl

/-- `A162740` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A162740 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A162740 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A162740
