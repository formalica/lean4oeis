# OEIS Formalization Library — Design Spec


# Defs.lean file

Each sequence gets its own **namespace** (not a shared structure).

For sequence `A000056`:

- `A000056.retType`: always `Nat` or `Int`.
- `A000056.argType`: `Nat`, `Int`, `PNat`, or a subtype of `Nat`/`Int`.
- `A000056.offset`: usually `0` or `1`; negative offsets rare, not a priority.
- `A000056 : arg → ret` — main definition.
- `A000056.fn : Nat → ret` — only added if `argType` is not `Int` or a subtype of `Int`.
- `A000056.fz : Int → ret` — always present. Total, junk value outside real domain. Used for composition.
- `A000056.prop : arg → ret → Prop` — relation defining the sequence.
- `A000056.prop_correct (n : arg) : prop n (A000056 n)` — proves that the main definition satisfies the proposition. Typically reflexivity (`rfl`) for computable sequences, or follows from the definition for non-computable ones.
- `A000056.fn_eq_fz`: proves `.fn` and `.fz` agree on overlapping domain.
- `A000056.fn_eq` / `A000056.fz_eq`: relate the helper functions back to the main definition.

## Definition order (computable vs non-computable)

- **Computable**: define `A000056` (and `fn`/`fz`) directly, then define `A000056.prop` in terms of it.
- **Non-computable**: define `A000056.prop` first, then obtain `A000056` via `Classical.choice` (needs an existence proof, you can fill proof of prop_ex by sorry).

## Composition rule

- Composed formulas always call `.fz` on every sequence involved, regardless of `argType`.
- `.fn` / main def (`arg → ret`) are for direct use only, when the argument's type is statically known to match — not for composition.

## Known issues (accepted tradeoffs)

- **Junk ambiguity**: `fz` returns a junk value (`0`) outside a sequence's real domain. If `0` is also a genuine output (e.g. `fib 0 = 0`), the two cases are indistinguishable from output alone. Any proof needing to tell them apart must state the domain condition explicitly (e.g. `n ≥ offset`), never infer it from the output.
- **Coherence**: `fn`, `fz`, and the main def must agree on overlapping inputs. Avoid a separate proof burden by defining `fn` and the main def *in terms of* `fz`, not independently.
- **argType proof cost**: if `argType` is `PNat` or a subtype, constructing a value of that type (to call `fn`/main def) requires a side proof. `fz` has no such cost — this is the reason composition always uses `fz`.
- This tradeoff (composition-free vs. junk-ambiguity-free) is inherent given `retType` is fixed to `Nat`/`Int`; removing the ambiguity (e.g. via `Option`) would reintroduce composition friction.



# Data.lean file

Each sequence may have a separate `Data.lean` file containing concrete data and related theorems.

For sequence `A000056`:

- `A000056.data : List ret` — a finite list of known values, typically up to some index.
- **Theorems** (all marked `@[simp]` for automation):
  - `data_eq {n : arg} {h : n < 28} : A000056 n = data[...]` — relates the main definition to the data list for indices within the data range.
  - `data_eq_fn {n : Nat} {...} {h : n < 28} : A000056.fn n = data[n-1]!` — relates `.fn` to the data list (only if `.fn` exists). reuse data_eq to prove this.
  - `data_eq_fz {n : Int} {...} {h : n < 28} : A000056.fz n = data[n.toNat-1]!` — relates `.fz` to the data list. reuse data_eq to prove this.

## Data proofs

- Proofs typically use `interval_cases` or `decide` to exhaustively verify small finite ranges for computable functions and always include domain conditions (e.g., `h : n < 28`) where 28 = data.length
- For non computable we often need to prove for each value setaratelly and it is hard to prove for all values in the range. So in this case we can prove them in separate theorems and use them inside data_eq theorem. `h : n < 3` will be range for which we proved data_eq.

