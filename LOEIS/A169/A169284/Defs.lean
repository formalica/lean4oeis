import OEISLib.Coxeter

/-!
# A169284

Number of reduced words of length n in Coxeter group on 31 generators S_i with relations (S_i)^2 = (S_i S_j)^29 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=31` `r=29`. The rational generating function is ` (t^29 + 2t^{28}+…+1) / (435·t^29 - 29·(t^{28}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A169284

/-- Number of generators `g` of `A169284`. -/
abbrev gParam : Nat := 31

/-- Edge label `r` of `A169284`. -/
abbrev rParam : Nat := 29

/-- `C(g-1,2)` for `A169284`. -/
abbrev c1Param : Nat := 435

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A169284` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A169284`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A169284

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A169284 : A169284.argType → A169284.retType := fun n =>
  OEISLib.Coxeter.coxSeq A169284.gParam A169284.rParam n

namespace A169284

/-- Relation that defines `A169284`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A169284 n) := rfl

/-- `A169284` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A169284

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A169284 n := rfl

/-- `A169284` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A169284 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A169284 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A169284
