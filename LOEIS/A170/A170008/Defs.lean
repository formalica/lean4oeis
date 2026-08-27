import OEISLib.Coxeter

/-!
# A170008

Number of reduced words of length n in Coxeter group on 47 generators S_i with relations (S_i)^2 = (S_i S_j)^35 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=47` `r=35`. The rational generating function is ` (t^35 + 2t^{34}+…+1) / (1035·t^35 - 45·(t^{34}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A170008

/-- Number of generators `g` of `A170008`. -/
abbrev gParam : Nat := 47

/-- Edge label `r` of `A170008`. -/
abbrev rParam : Nat := 35

/-- `C(g-1,2)` for `A170008`. -/
abbrev c1Param : Nat := 1035

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 14

/-- Index type of `A170008` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A170008`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A170008

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A170008 : A170008.argType → A170008.retType := fun n =>
  OEISLib.Coxeter.coxSeq A170008.gParam A170008.rParam n

namespace A170008

/-- Relation that defines `A170008`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A170008 n) := rfl

/-- `A170008` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A170008

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A170008 n := rfl

/-- `A170008` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A170008 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A170008 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A170008
