import LOEIS.A142.A142041.Defs

set_option maxRecDepth 4096

/-!
# A142041 — program transcriptions (`Equiv_ffbb19f73bb85eac`)

Alternative computable definitions transcribed from the OEIS program snippets of this sequence:

* `%T Select[Range[15, 20000, 32], PrimeQ] (* _Vladimir Joseph Stephan Orlovsky_, Jun 24 2011 *)`
* `%O (PARI) is(n)=isprime(n) && n%32==15 \\ _Charles R Greathouse IV_, Jul 03 2016`

Everything delegates to the shared library `OEISLib.Residue`, so the bridges to the main definition are proved once there and instantiated here.
-/

namespace A142041

/-- The canonical bounded enumeration (transcription of the Magma list comprehension and of `Select[Range[…], PrimeQ]`): every member of the class up to `searchBound`, increasing. -/
def programList : List Nat := OEISLib.Residue.membersUpTo aRes modulus searchBound

/-- `programList` is the generic bounded enumeration (definitionally). -/
theorem programList_eq :
    programList = OEISLib.Residue.membersUpTo aRes modulus searchBound := rfl

/-- **formula_eq** (main bridge): reading `programList` position by position is exactly the main definition. -/
theorem formula_eq (i : Nat) (h : i < programList.length) :
    programList[i]? = some (A142041 ⟨i + 1, by omega⟩) := by
  have h1 : programList[i]? =
      (OEISLib.Residue.membersUpTo aRes modulus searchBound)[i]? := rfl
  have h2 : A142041 ⟨i + 1, by omega⟩ =
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

end A142041
