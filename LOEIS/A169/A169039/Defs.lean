import OEISLib.Coxeter

/-!
# A169039

Number of reduced words of length n in Coxeter group on 26 generators S_i with relations (S_i)^2 = (S_i S_j)^24 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=26` `r=24`. The rational generating function is ` (t^24 + 2t^{23}+…+1) / (300·t^24 - 24·(t^{23}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A169039

/-- Number of generators `g` of `A169039`. -/
abbrev gParam : Nat := 26

/-- Edge label `r` of `A169039`. -/
abbrev rParam : Nat := 24

/-- `C(g-1,2)` for `A169039`. -/
abbrev c1Param : Nat := 300

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A169039` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A169039`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A169039

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A169039 : A169039.argType → A169039.retType := fun n =>
  OEISLib.Coxeter.coxSeq A169039.gParam A169039.rParam n

namespace A169039

/-- Relation that defines `A169039`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A169039 n) := rfl

/-- `A169039` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A169039

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A169039 n := rfl

/-- `A169039` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A169039 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A169039 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A169039
