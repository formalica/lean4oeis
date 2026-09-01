# OEISLib — per-sequence file shape

For each OEIS sequence `<name>` (its A-number, e.g. `A000027`) the
formalization lives in the directory `LOEIS/<bucket>/<name>/`, where
`bucket = <name>.take 4` (e.g. `LOEIS/A000/A000027/`).

Files:

- `Defs.lean` — the main definition and its standard API.
- `Data.lean` — imports `Defs.lean`; the known terms and theorems about them.
- `Equiv_<hash>.lean` / `Basic_<hash>.lean` — import `Defs.lean`; one file per
  alternative formula (hash defined below).

All declarations are inside `namespace <name>`, except the main definition,
which is at top level and is named `<name>`.

## Naming and type resolution

- Type abbrevs start with a capital letter: `ArgType`, `RetType`,
  `FlatArgType`, `FlatRetType`. Every other declaration — values, functions,
  theorems, and the offset constants `offset` / `flatOffset` — starts
  lowercase. The namespace and the top-level main definition are named
  `<name>` (the A-number).
- Signatures in this document use the placeholders `ArgType`, `RetType`,
  `FlatArgType`, `FlatRetType`. In generated code these placeholders must be
  resolved to concrete Lean types, and every declaration other than the
  `abbrev` definitions themselves must state its types concretely — including
  variable binders in theorems. A generated signature must never mention an
  abbrev name.

Type resolution rules:

- **Index type of one argument**, from its start index (the smallest index
  the argument ranges over):
  - start `0` → `Nat`
  - start `1` → `PNat`
  - start `k ≥ 2` → `{n : Nat // k ≤ n}`
  - start `k < 0` → `{n : Int // k ≤ n}`

  Subtypes are allowed wherever an index type appears (including components
  of a table index).
- **ArgType.**
  - Scalar: resolved by the index rule from the sequence offset (first number
    of the `%O` line).
  - Table: `T1 × T2`, where `T1` is resolved from the start index of `n` and
    `T2` from the start index of `k` (determined per the priority table in
    §2).
  - Decimal: `Unit`.
- **RetType** — `Int` if at least one listed term is negative, otherwise
  `Nat`; for decimal sequences it is `Real`.
- **Flat view.** Tables (read row by row) and decimal constants (read digit
  by digit) also have a flat, single-index view; scalar sequences do not. It
  is resolved like a scalar sequence:
  - `FlatArgType` — from `flatOffset` by the index rule.
  - `FlatRetType` — the type of the listed values: equal to `RetType` for
    tables; `Nat` (digits) for decimal sequences.
  - `flatOffset` — the flat index of the first listed term:
    for a decimal sequence it is the digit position of the first listed
    digit (first number of `%O`; usually `0`);
    for a table it is `0` by convention — the first listed cell is flat
    position `0`, and `flatData p` is the `p`-th term of the listing.

Every total extension (`fn`, `fz`, and their flat/table analogues) returns a
junk value (`0` of the return type) on arguments outside the real domain.

## Main definition vs proposition

Applies to all three sequence shapes.

- If the title (`%N`) states a rule that can be written directly as a Lean
  function (including over `Real`), that function is the main definition:
  define `<name>` first. `prop` is defined after it, as the relation that
  characterizes the sequence (the pointwise form `prop n z := z = <name> n`
  is always acceptable); then `prop_correct` holds by `rfl`.
- Otherwise the sequence is defined propositionally: define `prop` first,
  prove (or leave as `sorry`) that exactly one value satisfies it for each
  index, and obtain `<name>` via `Classical.choice`; `prop_correct` follows
  from the construction.

## Hashes of Equiv / Basic files

The hash is computed from the **original unformalized formula text**, never
from the formalized Lean code:

- `formulaHash(text) = hex(String.hash text)` — Lean core `String.hash`,
  rendered as 16 lowercase hexadecimal digits
  (`Scripts/OeisIngest/Parse.lean`).
- The hashed text is exactly the fragment of the source that the
  parser/template recognizes as the formula (its matched snippet).
  Surrounding human-language prose, author names and comments are skipped.
- When one `Equiv` file transcribes several recognized fragments, its
  file-name hash is `formulaHash` of those fragments joined with `"\n"`;
  each fragment additionally keeps its own per-fragment hash in the
  `formula` table.

## Alternative definitions and property theorems (`Equiv_<hash>.lean` / `Basic_<hash>.lean`)

Common to all three sequence shapes.

An `Equiv_<hash>.lean` file contains one alternative **full** definition of
the sequence, named `formula`, together with `theorem formula_eq`, in
exactly one of the two following forms:

1. **Value form.** `formula` has the exact signature of one value-defining
   declaration present in `Defs.lean`, and `formula_eq` states pointwise
   equality with that declaration on its whole domain:
   - main definition: `formula : ArgType → RetType`,
     `formula_eq (n : ArgType) : formula n = <name> n`;
   - `fn`: `formula : Nat → RetType`,
     `formula_eq (n : Nat) : formula n = fn n`;
   - `fz`: `formula : Int → RetType`,
     `formula_eq (n : Int) : formula n = fz n`;
   - the flat analogues `flat`, `flatFn`, `flatFz` the same way
     (`FlatArgType` for `flat`, `Nat` for `flatFn`, `Int` for `flatFz`);
   - for a decimal constant the main signature is nullary:
     `formula : RetType`, `formula_eq : formula = <name>`.
2. **Proposition form.** `formula` has the signature of `prop` (or
   `flatProp`): `formula : ArgType → RetType → Prop` (flat:
   `FlatArgType → FlatRetType → Prop`), and `formula_eq` states logical
   equivalence for all parameters:
   `formula_eq (n : ArgType) (z : RetType) : formula n z ↔ prop n z`
   (flat analogue: `formula n z ↔ flatProp n z`).

Mathematics shared between members of a family is placed in `OEISLib` and
called from the generated file, not duplicated per sequence.

Every unproved theorem in an `Equiv` or `Basic` file is closed with `sorry`
**only after** a check (`interval_cases`, or `decide`/`norm_num` where
applicable) that the statement holds for every index covered by the data;
the check must fail — and thereby reject the formula — if any data point
contradicts it.

A formula that states a property but does **not** fully determine the
sequence produces a `Basic_<hash>.lean` file: theorems only, no
`def formula`.

## 1. Simple scalar sequences

Sequences whose terms are `Nat`/`Int` valued and which have exactly one index
argument — i.e. neither `tabl`/`tabf` nor `cons`.

### Defs.lean
- `abbrev ArgType`, `abbrev RetType` (resolved by the rules above), and
  `abbrev offset : Int`.
- `def <name> : ArgType → RetType` — the main definition, per the
  main-definition rule above.
- `def prop : ArgType → RetType → Prop` — the defining relation.
- `def fn : Nat → RetType` — total extension to `Nat`: agrees with
  `<name>` on arguments that correspond to an in-domain index, junk `0`
  otherwise. Omitted when `offset < 0` (when `ArgType` is an `Int` subtype).
- `def fz : Int → RetType` — total extension to `Int`: agrees with
  `<name>` on in-domain indices, junk `0` otherwise. Always present.
  Any formula that references another sequence must call that sequence's
  `fz` with an `Int` argument; composition never uses the main definition
  or `fn`.
- `theorem prop_correct (n : ArgType) : prop n (<name> n)`.
- Coherence: `theorem fn_eq` (`fn` agrees with `<name>` under the domain
  hypothesis), `theorem fz_eq` (`fz` agrees with `<name>` under the domain
  hypothesis), `theorem fn_eq_fz` (`fn` and `fz` agree on their overlapping
  domain). To keep these proofs cheap, define `fn` and, where possible,
  `<name>` itself in terms of `fz`.

### Data.lean
- `def data : List RetType` — all terms OEIS provides, in order:
  `data[i]` is the term at OEIS index `offset + i`.
- `@[simp] theorem data_eq` relates `<name>` to `data` on the data range;
  `theorem data_eq_fn` and `theorem data_eq_fz` relate `fn` and `fz` to
  `data`, and are proved from `data_eq`. Each theorem carries a bound
  hypothesis restricting the index to the data range; the list position is
  the argument index minus `offset`.
- Proofs use `decide` / `interval_cases`. For non-computable sequences,
  prove one lemma per value and combine them in `data_eq`.

Alternative definitions go in `Equiv_<hash>.lean` per the common rule above
(available signatures: main definition, `fn`, `fz`, `prop`).

## 2. Table sequences (`tabl`)

Two-argument sequences `T(n,k)`, whose terms OEIS lists row by row.

**`tabf` sequences are skipped for now.** Their offsets, their dimension,
and their structure are not known; they are not formalized until that is
figured out.

### Start indices of n and k

Determined in this priority order; the first source that answers a
question wins:

| Priority | Source | What it gives |
| --- | --- | --- |
| 1 | `%O` line, first number | start index of **n** |
| 2 | Name text such as `0 <= k <= n` or `1 <= k <= n` | start index of **k** (also the end index of k) |
| 3 | Formula such as `T(n,0) = ...` or `T(n,1) = ...` | start index of **k** |
| 4 | Code such as `for n=0.. for k=0..n` or `n=1.. k=1..n` | start indices of both **n** and **k** |
| 5 | Guess: **k** starts at the same index as **n** | used only if nothing else says |

### Defs.lean
- `abbrev ArgType := T1 × T2` — pair of the index types of `n` and `k`,
  each resolved from its own start index by the index rule; either
  component may itself be a subtype (e.g. `PNat × {n : Nat // 2 ≤ n}`).
  `abbrev RetType`, `abbrev offset : Int` (the start index of `n`),
  `abbrev flatOffset : Int := 0`.
- `def <name> : ArgType → RetType` — the main two-argument definition
  (takes the pair), per the main-definition rule.
- `def fn : Nat → Nat → RetType` — total, all arguments `Nat`, junk `0`
  outside the domain; omitted when either component of `ArgType` is an
  `Int` subtype.
- `def fz : Int → Int → RetType` — total, all arguments `Int`, junk `0`
  outside the domain; always present; used for composition.
- `def prop : ArgType → RetType → Prop`, `theorem prop_correct`, and
  coherence theorems relating `fn` and `fz` to the main definition.
- Flat (row-by-row reading order) API, in `namespace <name>`:
  `abbrev FlatArgType`, `abbrev FlatRetType` (equal to `RetType`),
  `def flat : FlatArgType → FlatRetType`,
  `def flatFn : Nat → FlatRetType`,
  `def flatFz : Int → FlatRetType`,
  `def flatProp : FlatArgType → FlatRetType → Prop`,
  and theorems `flat_prop_correct`, `flat_fn_eq`, `flat_fz_eq`,
  `flat_fn_eq_fz` — the flat analogues of the scalar coherence theorems.
- A bridge theorem states that, under the row-major bijection between flat
  positions and index pairs in the table domain, `flat` at that position
  equals `<name>` applied to that pair.

### Data.lean
- `def flatData : List FlatRetType` — the terms in OEIS listing order;
  theorems `flat_data_eq`, `flat_data_eq_fn`, `flat_data_eq_fz`, each with
  a bound hypothesis restricting the flat index to the data range.

Alternative definitions go in `Equiv_<hash>.lean` per the common rule above
(available signatures: main two-argument definition, `fn`, `fz`, `flat`,
`flatFn`, `flatFz`, `prop`, `flatProp`).

## 3. Decimal-number sequences (`cons`)

Sequences whose keyword list (`%K`) contains `cons`: the sequence is one
real constant, and the listed terms are the digits of its decimal
expansion.

### Defs.lean
- `abbrev ArgType := Unit` (`()`), `abbrev RetType := Real`.
- `def <name> : RetType` — the constant itself, with no argument, per the
  main-definition rule.
- The constant has no index, so it has no `fn`, `fz`, or `prop` of its
  own; the index-based API lives on the flat digit view:
  `abbrev flatOffset : Int` (digit position of the first listed digit),
  `abbrev FlatArgType` (resolved from `flatOffset`),
  `abbrev FlatRetType := Nat`,
  `def flat : FlatArgType → Nat` (digit at the given position),
  `def flatFn : Nat → Nat`,
  `def flatFz : Int → Nat` (junk `0` outside the domain),
  `def flatProp : FlatArgType → Nat → Prop`,
  and theorems `flat_prop_correct`, `flat_fn_eq`, `flat_fz_eq`,
  `flat_fn_eq_fz`.
- A bridge theorem states that for every digit position in the domain,
  `flat` at that position equals the corresponding digit of the decimal
  expansion of `<name>`.

### Data.lean
- `def flatData : List Nat` — the digits in listing order; theorems
  `flat_data_eq`, `flat_data_eq_fn`, `flat_data_eq_fz`, each with a bound
  hypothesis restricting the flat index to the data range.

Alternative definitions go in `Equiv_<hash>.lean` per the common rule above
(available signatures: the nullary main definition for closed forms of the
constant, and `flat` / `flatFn` / `flatFz` / `flatProp` for alternative
digit formulas).
