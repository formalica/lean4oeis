import OEISLib.Coxeter

/-!
# A167988

Number of reduced words of length n in Coxeter group on 49 generators S_i with relations (S_i)^2 = (S_i S_j)^16 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=49` `r=16`. The rational generating function is ` (t^16 + 2t^{15}+…+1) / (1128·t^16 - 47·(t^{15}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A167988

/-- Number of generators `g` of `A167988`. -/
abbrev gParam : Nat := 49

/-- Edge label `r` of `A167988`. -/
abbrev rParam : Nat := 16

/-- `C(g-1,2)` for `A167988`. -/
abbrev c1Param : Nat := 1128

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 14

/-- Index type of `A167988` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A167988`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A167988

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A167988 : A167988.argType → A167988.retType := fun n =>
  OEISLib.Coxeter.coxSeq A167988.gParam A167988.rParam n

namespace A167988

/-- Relation that defines `A167988`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A167988 n) := rfl

/-- `A167988` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A167988

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A167988 n := rfl

/-- `A167988` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A167988 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A167988 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A167988
