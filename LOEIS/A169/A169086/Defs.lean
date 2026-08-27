import OEISLib.Coxeter

/-!
# A169086

Number of reduced words of length n in Coxeter group on 25 generators S_i with relations (S_i)^2 = (S_i S_j)^25 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=25` `r=25`. The rational generating function is ` (t^25 + 2t^{24}+…+1) / (276·t^25 - 23·(t^{24}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A169086

/-- Number of generators `g` of `A169086`. -/
abbrev gParam : Nat := 25

/-- Edge label `r` of `A169086`. -/
abbrev rParam : Nat := 25

/-- `C(g-1,2)` for `A169086`. -/
abbrev c1Param : Nat := 276

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A169086` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A169086`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A169086

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A169086 : A169086.argType → A169086.retType := fun n =>
  OEISLib.Coxeter.coxSeq A169086.gParam A169086.rParam n

namespace A169086

/-- Relation that defines `A169086`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A169086 n) := rfl

/-- `A169086` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A169086

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A169086 n := rfl

/-- `A169086` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A169086 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A169086 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A169086
