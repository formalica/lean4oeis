import Mathlib.Algebra.LinearRecurrence
import LOEIS.__BUCKET__.__SEQNAME__.Defs

/-!
# __SEQNAME__ — alternative definition `Equiv___HASH__`

__TITLE__

Machine translation of one Mathematica `LinearRecurrence` formula of the OEIS entry.

Original Mathematica source:

    __SOURCE__

Chosen index type: `__ARG_TYPE__`. Value type: `Int`.
-/

namespace __SEQNAME__.Equiv___HASH__

/-- The linear recurrence encoded by the Mathematica `LinearRecurrence` call. -/
def linearrec : LinearRecurrence Int :=
  ⟨__ORDER__, fun i =>
    match i with
    | 0 => __COEFF_0__
__COEFF_MATCHES__⟩

/-- The initial conditions of the Mathematica `LinearRecurrence` call. -/
def init : Fin __ORDER__ → Int := fun i =>
  match i with
  | 0 => __INIT_0__
__INIT_MATCHES__

/-- The formalized Mathematica formula, indexed from `0`. -/
def formula : __ARG_TYPE__ → Int :=
__FORMULA_BODY__

/-- The formalized Mathematica program agrees with the main definition. -/
theorem formula_eq (n : __SEQNAME__.argType) :
    formula n = __FORMULA_EQ_RHS__ := sorry

end __SEQNAME__.Equiv___HASH__
