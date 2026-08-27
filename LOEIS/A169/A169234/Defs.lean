import OEISLib.Coxeter

/-!
# A169234

Number of reduced words of length n in Coxeter group on 29 generators S_i with relations (S_i)^2 = (S_i S_j)^28 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=29` `r=28`. The rational generating function is ` (t^28 + 2t^{27}+…+1) / (378·t^28 - 27·(t^{27}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A169234

/-- Number of generators `g` of `A169234`. -/
abbrev gParam : Nat := 29

/-- Edge label `r` of `A169234`. -/
abbrev rParam : Nat := 28

/-- `C(g-1,2)` for `A169234`. -/
abbrev c1Param : Nat := 378

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A169234` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A169234`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A169234

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A169234 : A169234.argType → A169234.retType := fun n =>
  OEISLib.Coxeter.coxSeq A169234.gParam A169234.rParam n

namespace A169234

/-- Relation that defines `A169234`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A169234 n) := rfl

/-- `A169234` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A169234

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A169234 n := rfl

/-- `A169234` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A169234 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A169234 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A169234
