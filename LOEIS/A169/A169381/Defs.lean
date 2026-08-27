import OEISLib.Coxeter

/-!
# A169381

Number of reduced words of length n in Coxeter group on 32 generators S_i with relations (S_i)^2 = (S_i S_j)^31 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=32` `r=31`. The rational generating function is ` (t^31 + 2t^{30}+…+1) / (465·t^31 - 30·(t^{30}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A169381

/-- Number of generators `g` of `A169381`. -/
abbrev gParam : Nat := 32

/-- Edge label `r` of `A169381`. -/
abbrev rParam : Nat := 31

/-- `C(g-1,2)` for `A169381`. -/
abbrev c1Param : Nat := 465

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A169381` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A169381`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A169381

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A169381 : A169381.argType → A169381.retType := fun n =>
  OEISLib.Coxeter.coxSeq A169381.gParam A169381.rParam n

namespace A169381

/-- Relation that defines `A169381`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A169381 n) := rfl

/-- `A169381` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A169381

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A169381 n := rfl

/-- `A169381` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A169381 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A169381 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A169381
