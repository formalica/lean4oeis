import OEISLib.Coxeter

/-!
# A170011

Number of reduced words of length n in Coxeter group on 50 generators S_i with relations (S_i)^2 = (S_i S_j)^35 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=50` `r=35`. The rational generating function is ` (t^35 + 2t^{34}+…+1) / (1176·t^35 - 48·(t^{34}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A170011

/-- Number of generators `g` of `A170011`. -/
abbrev gParam : Nat := 50

/-- Edge label `r` of `A170011`. -/
abbrev rParam : Nat := 35

/-- `C(g-1,2)` for `A170011`. -/
abbrev c1Param : Nat := 1176

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 14

/-- Index type of `A170011` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A170011`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A170011

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A170011 : A170011.argType → A170011.retType := fun n =>
  OEISLib.Coxeter.coxSeq A170011.gParam A170011.rParam n

namespace A170011

/-- Relation that defines `A170011`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A170011 n) := rfl

/-- `A170011` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A170011

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A170011 n := rfl

/-- `A170011` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A170011 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A170011 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A170011
