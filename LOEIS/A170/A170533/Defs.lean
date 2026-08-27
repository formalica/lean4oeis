import OEISLib.Coxeter

/-!
# A170533

Number of reduced words of length n in Coxeter group on 44 generators S_i with relations (S_i)^2 = (S_i S_j)^46 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=44` `r=46`. The rational generating function is ` (t^46 + 2t^{45}+…+1) / (903·t^46 - 42·(t^{45}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A170533

/-- Number of generators `g` of `A170533`. -/
abbrev gParam : Nat := 44

/-- Edge label `r` of `A170533`. -/
abbrev rParam : Nat := 46

/-- `C(g-1,2)` for `A170533`. -/
abbrev c1Param : Nat := 903

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 14

/-- Index type of `A170533` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A170533`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A170533

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A170533 : A170533.argType → A170533.retType := fun n =>
  OEISLib.Coxeter.coxSeq A170533.gParam A170533.rParam n

namespace A170533

/-- Relation that defines `A170533`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A170533 n) := rfl

/-- `A170533` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A170533

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A170533 n := rfl

/-- `A170533` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A170533 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A170533 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A170533
