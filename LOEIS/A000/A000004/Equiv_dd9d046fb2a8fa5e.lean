import LOEIS.A000.A000004.Defs

/-!
# A000004 — alternative definition `Equiv_dd9d046fb2a8fa5e`

The zero sequence.

Machine translation of one Maple program of the OEIS entry.

Original Maple source:

    A000004 := n->0;

Chosen index type: `Nat`. Value type: `Nat`.
-/

namespace A000004.Equiv_dd9d046fb2a8fa5e

def formula (n : Nat) : Nat := 0

/-- The formalized Maple program agrees with the main definition. -/
theorem formula_eq (n : A000004.argType) :
    formula n = A000004 n := sorry

end A000004.Equiv_dd9d046fb2a8fa5e
