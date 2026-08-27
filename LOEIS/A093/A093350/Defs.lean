import OEISLib.Residue

/-!
# A093350

Primes congruent to 6 mod 13.

OEIS offset `1`. Formalized by the `primeCongruent` template: the main definition delegates to the generic bounded enumeration `OEISLib.Residue.nthIn` of the primes congruent to `6` modulo `13`. The propositional characterization is `nth_spec`; the transcribed `%t`/`%o` programs live in the `Equiv_<hash>` files.
-/

namespace A093350

/-- Residue parameter `a` of `A093350`, exactly as in the OEIS title. -/
abbrev aRes : Nat := 6

/-- Modulus parameter `m` of `A093350`. -/
abbrev modulus : Nat := 13

/-- Search bound: the largest term published by OEIS at formalization time. -/
abbrev searchBound : Nat := 3217

/-- Index type of `A093350` (OEIS offset `1`). -/
abbrev argType : Type := PNat

/-- Value type of `A093350`. -/
abbrev retType : Type := Nat

/-- OEIS offset: the index of the first known term. -/
abbrev offset : Int := 1

end A093350

/-- Primes congruent to `6` mod `13`: the `n`-th member of the class (OEIS indexing starts at 1). Junk value `0` past the search bound. -/
def A093350 : A093350.argType → A093350.retType := fun n =>
  OEISLib.Residue.nthIn A093350.aRes A093350.modulus (n.val - 1) A093350.searchBound

namespace A093350

/-- Relation that defines `A093350`: `z` is the (`n - 1`)-th member (0-indexed) of the class up to the search bound. -/
def prop : argType → retType → Prop := fun n z =>
  OEISLib.Residue.nthIn aRes modulus (n.val - 1) searchBound = z

/-- The main definition satisfies its defining relation. -/
theorem prop_correct (n : argType) : prop n (A093350 n) := rfl

/-- **High-level characterization**: within the enumerated range, the `n`-th term is prime, congruent to `aRes` modulo `modulus`, and preceded by exactly `n - 1` smaller members of the class. -/
theorem nth_spec (n : argType)
    (h : n.val - 1 <
        (OEISLib.Residue.membersUpTo aRes modulus searchBound).length) :
    Nat.Prime (A093350 n) ∧ A093350 n % modulus = aRes ∧
      (OEISLib.Residue.membersUpTo aRes modulus (A093350 n - 1)).length =
        n.val - 1 :=
  OEISLib.Residue.nthIn_spec h

/-- `A093350` as a total function on `Nat`; junk value outside the domain. -/
def fn : Nat → retType := fun n => if h : 0 < n then A093350 ⟨n, h⟩ else 0

/-- `fn` agrees with the main definition. -/
theorem fn_eq (n : Nat) (h : 0 < n) : fn n = A093350 ⟨n, h⟩ := by
  unfold fn
  split
  · rfl
  · omega

/-- `A093350` as a total function on `Int`; junk value outside the domain.
Always used when composing sequences. -/
def fz : Int → retType := fun i => if h : 1 ≤ i then A093350 ⟨i.toNat, by omega⟩ else 0

/-- `fz` agrees with the main definition on the domain. -/
theorem fz_eq (i : Int) (h : 1 ≤ i) : fz i = A093350 ⟨i.toNat, by omega⟩ := by
  unfold fz
  split
  · rfl
  · omega

/-- `fn` and `fz` agree on the overlapping domain. -/
theorem fn_eq_fz (n : Nat) (h : 0 < n) : fn n = fz (n : Int) := by
  unfold fn fz
  split
  · split
    · congr 1
    · omega
  · omega

end A093350
