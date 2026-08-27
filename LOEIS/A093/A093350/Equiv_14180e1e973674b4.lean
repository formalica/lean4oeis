import LOEIS.A093.A093350.Defs

set_option maxRecDepth 4096

/-!
# A093350 — program transcriptions (`Equiv_14180e1e973674b4`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%T Select[Range[6, 20000, 13], PrimeQ] (* _Vladimir Joseph Stephan Orlovsky_, Jun 18 2011 *)`
* `%O (PARI) is(n)=isprime(n) && n%13==6 \\ _Charles R Greathouse IV_, Jul 01 2016`

Everything delegates to the shared library `OEISLib.Residue`, so the bridges to the main definition are proved once there and instantiated here.
-/

namespace A093350

/-- The canonical bounded enumeration (transcription of the Magma list comprehension and of `Select[Range[…], PrimeQ]`): every member of the class up to `searchBound`, increasing. -/
def programList : List Nat := OEISLib.Residue.membersUpTo aRes modulus searchBound

/-- `programList` is the generic bounded enumeration (definitionally). -/
theorem programList_eq :
    programList = OEISLib.Residue.membersUpTo aRes modulus searchBound := rfl

/-- **formula_eq** (main bridge): reading `programList` position by position is exactly the main definition. -/
theorem formula_eq (i : Nat) (h : i < programList.length) :
    programList[i]? = some (A093350 ⟨i + 1, by omega⟩) := by
  have h1 : programList[i]? =
      (OEISLib.Residue.membersUpTo aRes modulus searchBound)[i]? := rfl
  have h2 : A093350 ⟨i + 1, by omega⟩ =
      OEISLib.Residue.nthIn aRes modulus i searchBound := rfl
  have h' : i < (OEISLib.Residue.membersUpTo aRes modulus searchBound).length := h
  rw [h1, h2]
  rcases OEISLib.Residue.getElem?_nthIn aRes modulus i searchBound with hs | hz
  · exact hs
  · exact absurd (OEISLib.Residue.nthIn_pos h') (by rw [hz]; simp)

/-- Characteristic function of the class (transcription of the PARI one-liner). -/
def pariIs : Nat → Bool := OEISLib.Residue.isMember aRes modulus

/-- The PARI test decides membership in the residue class of primes: `n` is prime and congruent to `aRes` modulo `modulus`. -/
theorem pariIs_iff (n : Nat) :
    pariIs n = true ↔ Nat.Prime n ∧ n % modulus = aRes :=
  OEISLib.Residue.isMember_iff

/-- Every member of the canonical enumeration passes the PARI test. -/
theorem pariIs_of_mem {n : Nat} (h : n ∈ programList) : pariIs n = true :=
  (OEISLib.Residue.mem_membersUpTo.mp h).2

end A093350
