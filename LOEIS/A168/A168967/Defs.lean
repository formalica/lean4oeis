import OEISLib.Coxeter

/-!
# A168967

Number of reduced words of length n in Coxeter group on 50 generators S_i with relations (S_i)^2 = (S_i S_j)^22 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=50` `r=22`. The rational generating function is ` (t^22 + 2t^{21}+…+1) / (1176·t^22 - 48·(t^{21}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A168967

/-- Number of generators `g` of `A168967`. -/
abbrev gParam : Nat := 50

/-- Edge label `r` of `A168967`. -/
abbrev rParam : Nat := 22

/-- `C(g-1,2)` for `A168967`. -/
abbrev c1Param : Nat := 1176

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 14

/-- Index type of `A168967` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A168967`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A168967

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A168967 : A168967.argType → A168967.retType := fun n =>
  OEISLib.Coxeter.coxSeq A168967.gParam A168967.rParam n

namespace A168967

/-- Relation that defines `A168967`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A168967 n) := rfl

/-- `A168967` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A168967

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A168967 n := rfl

/-- `A168967` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A168967 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A168967 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A168967
