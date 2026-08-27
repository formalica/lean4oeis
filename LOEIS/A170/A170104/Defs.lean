import OEISLib.Coxeter

/-!
# A170104

Number of reduced words of length n in Coxeter group on 47 generators S_i with relations (S_i)^2 = (S_i S_j)^37 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=47` `r=37`. The rational generating function is ` (t^37 + 2t^{36}+…+1) / (1035·t^37 - 45·(t^{36}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A170104

/-- Number of generators `g` of `A170104`. -/
abbrev gParam : Nat := 47

/-- Edge label `r` of `A170104`. -/
abbrev rParam : Nat := 37

/-- `C(g-1,2)` for `A170104`. -/
abbrev c1Param : Nat := 1035

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 14

/-- Index type of `A170104` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A170104`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A170104

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A170104 : A170104.argType → A170104.retType := fun n =>
  OEISLib.Coxeter.coxSeq A170104.gParam A170104.rParam n

namespace A170104

/-- Relation that defines `A170104`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A170104 n) := rfl

/-- `A170104` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A170104

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A170104 n := rfl

/-- `A170104` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A170104 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A170104 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A170104
