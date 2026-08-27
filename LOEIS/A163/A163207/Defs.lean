import OEISLib.Coxeter

/-!
# A163207

Number of reduced words of length n in Coxeter group on 29 generators S_i with relations (S_i)^2 = (S_i S_j)^4 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=29` `r=4`. The rational generating function is ` (t^4 + 2t^{3}+…+1) / (378·t^4 - 27·(t^{3}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A163207

/-- Number of generators `g` of `A163207`. -/
abbrev gParam : Nat := 29

/-- Edge label `r` of `A163207`. -/
abbrev rParam : Nat := 4

/-- `C(g-1,2)` for `A163207`. -/
abbrev c1Param : Nat := 378

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A163207` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A163207`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A163207

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A163207 : A163207.argType → A163207.retType := fun n =>
  OEISLib.Coxeter.coxSeq A163207.gParam A163207.rParam n

namespace A163207

/-- Relation that defines `A163207`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A163207 n) := rfl

/-- `A163207` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A163207

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A163207 n := rfl

/-- `A163207` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A163207 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A163207 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A163207
