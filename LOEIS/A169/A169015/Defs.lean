import OEISLib.Coxeter

/-!
# A169015

Number of reduced words of length n in Coxeter group on 50 generators S_i with relations (S_i)^2 = (S_i S_j)^23 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=50` `r=23`. The rational generating function is ` (t^23 + 2t^{22}+…+1) / (1176·t^23 - 48·(t^{22}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A169015

/-- Number of generators `g` of `A169015`. -/
abbrev gParam : Nat := 50

/-- Edge label `r` of `A169015`. -/
abbrev rParam : Nat := 23

/-- `C(g-1,2)` for `A169015`. -/
abbrev c1Param : Nat := 1176

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 14

/-- Index type of `A169015` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A169015`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A169015

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A169015 : A169015.argType → A169015.retType := fun n =>
  OEISLib.Coxeter.coxSeq A169015.gParam A169015.rParam n

namespace A169015

/-- Relation that defines `A169015`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A169015 n) := rfl

/-- `A169015` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A169015

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A169015 n := rfl

/-- `A169015` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A169015 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A169015 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A169015
