import OEISLib.Coxeter

/-!
# A166416

Number of reduced words of length n in Coxeter group on 22 generators S_i with relations (S_i)^2 = (S_i S_j)^11 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=22` `r=11`. The rational generating function is ` (t^11 + 2t^{10}+…+1) / (210·t^11 - 20·(t^{10}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A166416

/-- Number of generators `g` of `A166416`. -/
abbrev gParam : Nat := 22

/-- Edge label `r` of `A166416`. -/
abbrev rParam : Nat := 11

/-- `C(g-1,2)` for `A166416`. -/
abbrev c1Param : Nat := 210

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A166416` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A166416`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A166416

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A166416 : A166416.argType → A166416.retType := fun n =>
  OEISLib.Coxeter.coxSeq A166416.gParam A166416.rParam n

namespace A166416

/-- Relation that defines `A166416`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A166416 n) := rfl

/-- `A166416` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A166416

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A166416 n := rfl

/-- `A166416` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A166416 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A166416 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A166416
