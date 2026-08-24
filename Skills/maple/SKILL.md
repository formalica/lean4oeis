# Maple → Lean 4 formalization

You translate Maple programs attached to OEIS sequences into Lean 4 + Mathlib definitions.

## What you are given

A batch of OEIS sequences. For each one:

- its A-number, title, OEIS offset, argument type and return type of the Lean main definition,
- the first known terms,
- one raw Maple block, exactly as it appears in the OEIS entry.

A single Maple block often contains **several independent programs** merged together
(a `proc`, then a `seq(...)` driver line, then an alternative approach, then a `printf` loop).

**Every one of them needs its own item.** Whatever you leave unclaimed is recorded in the
database as unformalized and reported back to you as a defect to fix.

## What you must return

A list of items. Each item covers **one** independent Maple program and has:

- `start_marker` — the first characters of that program, copied verbatim from the block.
- `end_marker` — the last characters of that program, copied verbatim, **including the
  trailing comment and author credit** when there is one.
- `lean_code` — the Lean 4 translation.
- `arg_kind` — the index type you chose.
- `computable` — whether `lean_code` is executable.

Plus a `skipped` list for programs you deliberately do not translate, each with a reason.

### The markers are checked mechanically

You never copy a whole program back — long verbatim copies drift. You delimit it instead:
we search the block for `start_marker`, then for `end_marker` at or after it, and the item
claims everything in between, inclusive.

Rules:

- Both markers must be **at least 6 characters**, and long enough to occur only once inside
  that block. 15–60 characters is the usual range.
- Copy them character for character: no re-indenting, no whitespace normalization, no typo
  fixes, no dropped `;` / `:`. Newlines inside the block are `\n`.
- `start_marker` must appear before `end_marker`.
- The spans of two items of the same sequence must **not overlap**.
- Extend `end_marker` through the trailing credit comment
  (`end proc: # _R. J. Mathar_, Nov 15 2014`) so no orphan attribution line is left over as
  a spurious unformalized fragment.

Example — this block holds two programs:

```maple
M := 100; s := [ 1,2,2 ]; ... A000002 := n->s[n];
# Alternative: based on the Cloitre formula:
A000002 := proc(n)
...
end proc: # _R. J. Mathar_, Nov 15 2014
```

Item 1: `start_marker = "M := 100; s := [ 1,2,2 ]"`, `end_marker = "A000002 := n->s[n];"`.
Item 2: `start_marker = "A000002 := proc(n)"`,
`end_marker = "end proc: # _R. J. Mathar_, Nov 15 2014"`.

### Skip, do not invent

Emit **no item** for parts of the block that are not a definition of the sequence:

- pure driver / printing lines (`seq(a(n), n=0..30);`, `lprint`, `printf`, `[seq(...)]`),
- comments (`# Alternative:`, attribution such as `# _Peter Luschny_, Aug 19 2020`),
- `with(...)` package loads on their own.

If a `proc` and the `seq(...)` line that calls it belong together, the item is the `proc`;
leave the driver line out.

Anything larger than that which you choose not to translate belongs in `skipped`, with the
reason — that is what stops it from being flagged as a missed program.

## The Lean code you write

```lean
def formula : <ArgType> → <RetType> := ...
```

Hard requirements:

1. The definition **must** be named `formula`. Exactly one `formula` per item.
2. The return type **must** be the sequence's `retType` (`Nat` or `Int`), given to you.
   Do not change it.
3. Helper definitions are allowed. Put them **before** `formula` and give them a
   `formula_`-prefixed name (`formula_aux`, `formula_step`, ...) so they cannot clash.
4. Do not write `theorem`, `example`, `#eval`, `#check`, `import`, `namespace`, `section`,
   `open`, or `set_option`. Imports and the surrounding namespace are added by the pipeline.
   `open ... in` immediately before `formula` is allowed if you need a scoped notation.
5. Recursion must be accepted by Lean: use structural recursion, or supply
   `termination_by` / `decreasing_by`. Maple's `option remember` is only memoization —
   it carries no meaning in Lean, translate the recurrence itself.
6. Prefer total, closed-form, executable code. `Finset.sum` / `Finset.prod` over
   `Finset.range` are executable. `Real`, `Classical.choice`, `Nat.nth`, `Nat.find`,
   `Set`, and infinite sums are **not**.

### Choosing `arg_kind`

The offset of the sequence decides which index types are allowed.

| offset | allowed `arg_kind` | Lean type |
| --- | --- | --- |
| `0` | `Nat` | `Nat` |
| `1` | `Nat`, `PNat`, `NatSub` | `Nat`, `PNat`, `{n : Nat // 1 ≤ n}` |
| `k ≥ 2` | `Nat`, `NatSub` | `Nat`, `{n : Nat // k ≤ n}` |
| `k < 0` | `Int`, `IntSub` | `Int`, `{n : Int // k ≤ n}` |

Pick `Nat` / `Int` when the formula is total and you can give a sensible value below the
offset. Pick the subtype when the formula only makes sense from the offset onwards
(a subtraction that would underflow, a division by `n - 1`, ...). With a subtype, the
index is `n.val`.

### Truncated subtraction

`Nat` subtraction truncates at `0`. `3 * n ^ 2 - 7 * n + 6` is **wrong** in `Nat` for
`n = 1`. Reorder so that every subtraction is applied after the additions:
`3 * n ^ 2 + 6 - 7 * n`. Do **not** patch it up with `if n = 0 then ... else ...` special
cases — reordering is the expected answer. If reordering cannot work, use an `Int`
intermediate and convert at the end (`(... : Int).toNat`), or choose a subtype `arg_kind`.

### Referring to other OEIS sequences

When a Maple program calls another sequence, e.g. `A000108(k)`, use the Lean API we give
you for that sequence. Three forms exist and they agree wherever both are defined:

- `A000108` — the main definition, argument type is that sequence's own `argType`
  (possibly `PNat` or a subtype), so you may have to build the argument.
- `A000108.fn : Nat → retType` — total on `Nat`, junk value below the offset.
- `A000108.fz : Int → retType` — total on `Int`, junk value outside the domain.

`fn` and `fz` are the convenient ones inside a sum, because the summation index is a plain
`Nat` / `Int`. Use them freely. Their bodies are still `sorry`, so the pipeline executes your
code against a stand-in built from the terms OEIS lists for that sequence — that is handled
for you. The only consequence is that a translation reaching far past the listed terms of a
referenced sequence cannot be validated, so keep the index arithmetic tight.

Never define a sequence's own value by calling itself through this API — for a recurrence,
write the recursion inside `formula`.

### When you cannot produce executable code

Set `computable = false` and put the best non-executable Lean you can into `lean_code`
(generating functions, real/complex analysis, asymptotics, `Filter.Tendsto`, ...).
Mark it `noncomputable def formula ...` when it is still a function. Such items are stored
but not compiled, so a rough but honest translation is better than a wrong executable one.
Do **not** set `computable = false` just because the translation is hard.

## Maple function table

Only the rows relevant to this batch are shown.

<!-- BEGIN FUNCTION TABLE -->
| Maple | Usage | Lean 4 / Mathlib | Notes |
| --- | --- | --- | --- |
| `proc`, `end`, `local`, `option`, `procname` | `f := proc(n) ... end proc:` | `def formula : Nat → Nat := fun n => ...` | `procname` is the recursive self-reference: `formula` itself. `option remember` is memoization only, drop it. `local x;` declares locals, use `let`. |
| `add` | `add(f(k), k=a..b)` | `∑ k ∈ Finset.Icc a b, f k` | Empty when `b < a`, same as Maple. For `k=0..n` prefer `∑ k ∈ Finset.range (n+1), f k`. |
| `mul` | `mul(f(k), k=a..b)` | `∏ k ∈ Finset.Icc a b, f k` | Same range convention as `add`. |
| `sum`, `product` | `sum(f(k), k=a..b)` | `∑ k ∈ Finset.Icc a b, f k` | Symbolic in Maple; when the bounds are infinite (`k=0..infinity`) this is a generating function, set `computable = false`. |
| `seq` | `seq(f(n), n=a..b)` | *(usually drop it)* | Almost always the driver that prints the terms, not a definition. Only translate it if it is the sole content of a program, as `(List.range (b+1)).map f`. |
| `binomial` | `binomial(n, k)` | `Nat.choose n k` | `n.choose k`. For `Int` arguments or `n < k` semantics use `Nat.choose` on `.toNat` after guarding. |
| `factorial`, `!` | `factorial(n)`, `n!` | `Nat.factorial n` | `n !` with the `Nat.factorial` notation open, otherwise `Nat.factorial n`. |
| `floor`, `iquo`, `trunc` | `floor(n/2)`, `iquo(a,b)` | `n / 2`, `a / b` | `Nat` and `Int` division in Lean already truncates toward zero for `Nat`; `Int./` is T-division, `Int.fdiv` is floor division. For `floor` of an exact rational on naturals, plain `/` is right. |
| `ceil` | `ceil(a/b)` | `(a + b - 1) / b` | On `Nat` with `b > 0`. Avoid `⌈·⌉` (needs `Rat`/`Real`, not executable here). |
| `irem`, `modp`, `mod` | `irem(a,b)`, `a mod b` | `a % b` | `Nat.mod` / `Int.emod`. Maple's `mod` on negatives is the positive representative, matching `Int.emod`. |
| `igcd`, `gcd` | `igcd(a,b)` | `Nat.gcd a b` | `Nat.lcm` for `ilcm`. `gcd` on polynomials is not this. |
| `isprime` | `isprime(n)` | `Nat.Prime n` | Decidable, so `if Nat.Prime n then _ else _` works and is executable via `decide`. In a `Finset.filter` use `Finset.filter (fun k => Nat.Prime k)`. |
| `ithprime` | `ithprime(k)` | `Nat.nth Nat.Prime (k - 1)` | **Not executable.** Maple is 1-based, `Nat.nth` is 0-based. Prefer restructuring to avoid it; otherwise set `computable = false`. |
| `nextprime`, `prevprime` | `nextprime(n)` | `Nat.nth Nat.Prime (...)` | Not executable in Mathlib. Set `computable = false` unless you can avoid it. |
| `sqrt`, `isqrt` | `sqrt(n)` | `Nat.sqrt n` | `Nat.sqrt` is integer square root and executable. Only use `Real.sqrt` when the value is genuinely irrational, and then set `computable = false`. |
| `issqr` | `issqr(n)` | `Nat.sqrt n * Nat.sqrt n = n` | Executable. `IsSquare n` is the propositional form but is not decidable by `decide` efficiently. |
| `abs` | `abs(x)` | `\|x\|`, `Int.natAbs x` | Use `Int.natAbs` when the result must be a `Nat`. |
| `max`, `min` | `max(a,b)` | `max a b`, `min a b` | Variadic in Maple; fold: `max a (max b c)`. |
| `nops` | `nops(L)` | `L.length`, `s.card` | `List.length` for lists, `Finset.card` for sets. |
| `op` | `op(i, L)` | `L[i - 1]!` | Maple lists are 1-based, Lean lists are 0-based. `op(L)` alone splices all entries. |
| `select`, `map` | `select(p, L)`, `map(f, L)` | `L.filter p`, `L.map f` | `select` keeps the elements satisfying `p`. |
| `ifactors`, `numtheory[factorset]` | `ifactors(n)[2]` | `Nat.factorization n`, `n.primeFactorsList` | `Nat.factorization n p` is the exponent of `p`. `Nat.primeFactorsList` is the multiset of prime factors as a sorted list, executable. |
| `numer`, `denom` | `numer(x)` | `Rat.num x`, `Rat.den x` | Only meaningful on `Rat`; converting to the sequence's `Nat`/`Int` return type is your job. |
| `convert` | `convert(x, T)` | *(type cast)* | `convert(n, base, 10)` → `Nat.digits 10 n`; `convert(L, `+`)` → `L.sum`; `convert(L, `*`)` → `L.prod`; `convert(x, rational)` → drop. |
| `evalf`, `simplify`, `expand`, `normal` | `evalf(x)` | *(drop)* | Maple evaluation control with no Lean counterpart. If `evalf` is what makes the result an integer (e.g. `floor(evalf(...))`), the underlying value is real: set `computable = false`. |
| `series`, `coeff`, `coeftayl`, `taylor` | `coeff(series(f, x, n+1), x, n)` | *(generating function)* | Power-series extraction. There is no executable Mathlib route; set `computable = false` and write the coefficient statement using `PowerSeries.coeff`. |
| `printf`, `lprint`, `print`, `with` | `printf("%d", a)` | *(drop)* | Output and package loading. Never produce an item for these alone. |
| `combinat` | `combinat[fibonacci](n)`, `combinat[stirling2](n,k)` | `Nat.fib n`, `Nat.stirlingSecond n k` | `combinat[binomial]` → `Nat.choose`; `combinat[numbpart]` → `Nat.partition` is not executable, set `computable = false`; `combinat[bell]` → write the recurrence out. |
| `sort` | `sort(L)`, `sort(L, `>`)` | `L.mergeSort (· ≤ ·)` | Executable. Descending: `L.mergeSort (· ≥ ·)`. |
| `type`, `whattype` | `type(n, integer)`, `type(n, even)` | `n % 2 = 0`, `Nat.Prime n` | A predicate test. `type(x, even)` → `x % 2 = 0`, `type(x, odd)` → `x % 2 = 1`, `type(x, prime)` → `Nat.Prime x`, `type(x, integer)` is vacuous here. |
| `subs`, `eval` | `subs(x=3, f)` | *(inline the value)* | Symbolic substitution. Perform it yourself while translating; there is nothing to emit. |
| `ilog10`, `ilog2`, `length` | `ilog10(n)` | `(Nat.digits 10 n).length - 1` | `length(n)` on an integer is its decimal digit count, `(Nat.digits 10 n).length`. |
| `exp`, `log`, `ln`, `Pi`, `sin`, `cos` | `floor(exp(n))` | `Real.exp`, `Real.log`, `Real.pi` | Genuinely real-valued: set `computable = false`. |
| `Matrix`, `LinearAlgebra` | `Matrix(n, n, f)` | `Matrix (Fin n) (Fin n) ℤ` | Usually a transfer-matrix power. `Matrix.of fun i j => ...`, entry `(M ^ k) i j`. Executable but slow; prefer unrolling the recurrence it encodes. |
| `rsolve`, `solve`, `msolve`, `dsolve` | `rsolve({a(n) = ...}, a(n))` | *(solve it yourself)* | Maple's solver. Translate the **recurrence being solved**, not the call. |
<!-- END FUNCTION TABLE -->
