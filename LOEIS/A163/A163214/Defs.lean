import OEISLib.Coxeter

/-!
# A163214

Number of reduced words of length n in Coxeter group on 31 generators S_i with relations (S_i)^2 = (S_i S_j)^4 = I.

OEIS offset `0`. Formalized by the `coxeter` template: the main definition delegates to the generic `OEISLib.Coxeter.coxSeq` with parameters `g=31` `r=4`. The rational generating function is ` (t^4 + 2t^{3}+…+1) / (435·t^4 - 29·(t^{3}+…+t)+1)`. The `%F`/`%t`/`%o` transcriptions live in the `Equiv_<hash>` file.
-/

namespace A163214

/-- Number of generators `g` of `A163214`. -/
abbrev gParam : Nat := 31

/-- Edge label `r` of `A163214`. -/
abbrev rParam : Nat := 4

/-- `C(g-1,2)` for `A163214`. -/
abbrev c1Param : Nat := 435

/-- Search bound (largest term index verified at formalization time). -/
abbrev searchBound : Nat := 15

/-- Index type of `A163214` (OEIS offset `0`). -/
abbrev argType : Type := Nat

/-- Value type of `A163214`. -/
abbrev retType : Type := Nat

/-- OEIS offset. -/
abbrev offset : Int := 0

end A163214

/-- Number of reduced words of length `n` in the Coxeter group on `gParam` generators with edge label `rParam` (main definition, computable via `OEISLib.Coxeter.coxSeq`). -/
def A163214 : A163214.argType → A163214.retType := fun n =>
  OEISLib.Coxeter.coxSeq A163214.gParam A163214.rParam n

namespace A163214

/-- Relation that defines `A163214`. -/
def prop : argType → retType → Prop := fun n m =>
  OEISLib.Coxeter.coxSeq gParam rParam n = m

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A163214 n) := rfl

/-- `A163214` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := A163214

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) : fn n = A163214 n := rfl

/-- `A163214` as a total function on `Int`; junk value outside the domain. -/
def fz : Int → retType := fun n => if 0 ≤ n then A163214 n.toNat else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (n : Int) (h : 0 ≤ n) : fz n = A163214 n.toNat := by
  simp only [fz, if_pos h]

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) : fn n = fz (n : Int) := by
  have hn : 0 ≤ (n : Int) := by omega
  simp only [fn, fz, if_pos hn]
  congr 1

end A163214
