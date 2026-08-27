import OEISLib.Coxeter

/-!
# A164741

Number of reduced words of length n in Coxeter group on 6 generators S_i with relations (S_i)^2 = (S_i S_j)^8 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=6` `r=8`. The rational generating function is ` (t^8 + 2t^{7}+…+1) / (10·t^8 - 4·(t^{7}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A164741

/-- Number of generators `g` of `A164741`. -/
abbrev gParam : Nat := 6

/-- Edge label `r` of `A164741`. -/
abbrev rParam : Nat := 8

/-- `C(g-1,2)` for `A164741`. -/
abbrev c1Param : Nat := 10

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 21

/-- Index type of `A164741` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A164741`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A164741

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A164741 : A164741.argType → A164741.retType := fun n =>
  OEISLib.Coxeter.coxSeq A164741.gParam A164741.rParam n

namespace A164741

/-- Relation that defines `A164741`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A164741 n) := rfl

/-- `A164741` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A164741

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A164741 n := rfl

/-- `A164741` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A164741 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A164741 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A164741
