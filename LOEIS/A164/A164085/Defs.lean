import OEISLib.Coxeter

/-!
# A164085

Number of reduced words of length n in Coxeter group on 40 generators S_i with relations (S_i)^2 = (S_i S_j)^6 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=40` `r=6`. The rational generating function is ` (t^6 + 2t^{5}+…+1) / (741·t^6 - 38·(t^{5}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A164085

/-- Number of generators `g` of `A164085`. -/
abbrev gParam : Nat := 40

/-- Edge label `r` of `A164085`. -/
abbrev rParam : Nat := 6

/-- `C(g-1,2)` for `A164085`. -/
abbrev c1Param : Nat := 741

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 14

/-- Index type of `A164085` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A164085`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A164085

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A164085 : A164085.argType → A164085.retType := fun n =>
  OEISLib.Coxeter.coxSeq A164085.gParam A164085.rParam n

namespace A164085

/-- Relation that defines `A164085`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A164085 n) := rfl

/-- `A164085` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A164085

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A164085 n := rfl

/-- `A164085` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A164085 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A164085 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A164085
