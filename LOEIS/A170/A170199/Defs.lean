import OEISLib.Coxeter

/-!
# A170199

Number of reduced words of length n in Coxeter group on 46 generators S_i with relations (S_i)^2 = (S_i S_j)^39 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=46` `r=39`. The rational generating function is ` (t^39 + 2t^{38}+…+1) / (990·t^39 - 44·(t^{38}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A170199

/-- Number of generators `g` of `A170199`. -/
abbrev gParam : Nat := 46

/-- Edge label `r` of `A170199`. -/
abbrev rParam : Nat := 39

/-- `C(g-1,2)` for `A170199`. -/
abbrev c1Param : Nat := 990

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 14

/-- Index type of `A170199` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A170199`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A170199

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A170199 : A170199.argType → A170199.retType := fun n =>
  OEISLib.Coxeter.coxSeq A170199.gParam A170199.rParam n

namespace A170199

/-- Relation that defines `A170199`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A170199 n) := rfl

/-- `A170199` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A170199

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A170199 n := rfl

/-- `A170199` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A170199 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A170199 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A170199
