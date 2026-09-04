import GenExpr.Api
import GenExprTests

/-!
The acceptance corpus: every "important corner case" and "multiplication corner case" from the
specification, as data.

Kept separate from the `#guard` suites so the runner can report coverage in one table.
-/

namespace GenExprTests.Cases

open GenExpr

def N : FnTy := { args := [.nat], ret := .nat }
def NQ : FnTy := { args := [.nat], ret := .rat }
def NR : FnTy := { args := [.nat], ret := .real }
def R : FnTy := { args := [], ret := .real }
def Nc : FnTy := { args := [], ret := .nat }

/-- One entry of the corpus. `expect` is the body the parser should settle on, or `none` when the
line must be rejected. -/
structure Case where
  name : String
  input : String
  names : Array String := #["a"]
  types : Array FnTy := #[N]
  values : List Int := []
  allowed : Nat := 0
  custom : Array String := #[]
  expect : Option String
  expectDecl : Option String := none

private def customAlt (f : String) : Alt :=
  { key := f, template := f ++ " {0}", params := #[.nat], result := .nat, prec := 1023,
    argPrec := #[1024] }

private def custom2 (f : String) : Alt :=
  { key := f, template := f ++ " {0} {1}", params := #[.nat, .nat], result := .nat, prec := 1023,
    argPrec := #[1024, 1024] }

def corpus : Array Case := #[
  { name := "01 generating function in prose"
    input := "another words (1+2*x^4)/((1-x^3)*(1-x-x^2)). - _John Doe_, Dec 29 2012"
    names := #[], types := #[NQ]
    expect := some "(1 + 2 * (x : ℚ) ^ 4) / ((1 - (x : ℚ) ^ 3) * (1 - (x : ℚ) - (x : ℚ) ^ 2))" },
  { name := "02 0^0 = 1"
    input := "a(n) = 0^n + n", values := [1, 1, 2, 3, 4, 5]
    expect := some "0 ^ n + n" },
  { name := "03 nested sums"
    input := "a(n)=sum_(k=0)^n sum_(i=0)^n T(k,i)", custom := #["T2"]
    expect := some "∑ k ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1), T k i" },
  { name := "04 unbounded sum"
    input := "g = sum{k>=1} 1/k^2", names := #["g"], types := #[R]
    expect := some "∑' k : ℕ, 1 / (k + 1 : ℝ) ^ 2" },
  { name := "05 recursion with a stated domain"
    input := "a(n) = a(n-1)+n^2 for n > 1", values := [0, 1, 5, 14, 30, 55]
    expect := some "«self» (n - 1) + n ^ 2"
    expectDecl := some "def a : ℕ → ℕ\n  | 0 => 0\n  | n + 1 => a n + (n + 1) ^ 2" },
  { name := "06 division and double factorial"
    input := "a(n)=2*n+n/2+n!!"
    expect := some "2 * n + n / 2 + Nat.doubleFactorial n" },
  { name := "07 integral"
    input := "a = integral(x=0)^1 x^2", types := #[R]
    expect := some "∫ x in (0 : ℝ)..1, x ^ 2" },
  { name := "08 truncated subtraction"
    input := "a(n) = 3n^2 - 7*n + 6", values := [6, 2, 4, 12, 26, 46]
    expect := some "3 * n ^ 2 + 6 - 7 * n" },
  { name := "09 A084847, rational intermediates"
    input := "a(n) = 2*3^n+(n-2)*2^(2n-1)", values := [1, 4, 18, 86, 418, 2022]
    expect := some "⌊2 * 3 ^ n + ((n : ℚ) - 2) * 2 ^ (2 * (n : ℤ) - 1)⌋₊" },
  { name := "10 mod precedence"
    input := "a(n) = 3*n + (9*n mod 6 - 6)"
    expect := some "3 * n + (9 * n % 6 - 6)" },
  { name := "11 nested sqrt precedence"
    input := "a(n) = sqrt(6*n*(3*n + (-1)^n - 3)-3*(-1)^n + 5)/sqrt(2)", types := #[NR]
    expect := some
      ("(Int.sqrt (6 * (n : ℤ) * (3 * (n : ℤ) + (-1 : ℤ) ^ n - 3) - 3 * (-1 : ℤ) ^ n + 5) : ℝ)" ++
        " / (Nat.sqrt 2 : ℝ)") },
  { name := "12 constants"
    input := "res = sin(2*pi)*e", names := #["res"], types := #[R]
    expect := some "Real.sin (2 * Real.pi) * Real.exp 1" },
  { name := "13a power written before the arguments"
    input := "A(x) = 1 + T(x) - T^2(x)/2 + T(x^2)/2", names := #["A"], custom := #["T"]
    -- `T^2(x)` is `(T x)^2`; over ℕ the subtraction is moved past the additions.
    expect := some "1 + T x + T (x ^ 2) / 2 - T x ^ 2 / 2" },
  { name := "13b the same line without T is unparsable"
    input := "A(x) = 1 + T(x) - T^2(x)/2 + T(x^2)/2", names := #["A"]
    expect := none },
  { name := "15 subscript is the first argument"
    input := "a(n) = log_2(n)"
    expect := some "Nat.log 2 n" },
  { name := "16 a binder shadows the catalogue"
    input := "a(n) = Sum_{i=0..n} i"
    expect := some "∑ i ∈ Finset.range (n + 1), i" },
  { name := "17 absolute value"
    input := "a(n) = |n-1|", values := [1, 0, 1, 2, 3, 4]
    expect := some "((n : ℤ) - 1).natAbs" },
  { name := "18 auxiliary function"
    input := "b(n) = n^2+1; a(n) = b(b(b(n)))", values := [5, 26, 677]
    expect := some "b (b (b n))" },
  { name := "19 auxiliary constant"
    input := "a = c^c + c where c=floor(3^10/2^10)", types := #[Nc]
    expect := some "c ^ c + c" },
  { name := "20a implicit multiplication"
    input := "a(n) = n(n+1)/2", values := [0, 1, 3, 6, 10]
    expect := some "n * (n + 1) / 2" },
  { name := "20b glued factor"
    input := "a(n) = 2(n+1)", values := [2, 4, 6, 8]
    expect := some "2 * (n + 1)" },
  { name := "20c adjacent parentheses"
    input := "a(n) = (n+1)(n+2)", values := [2, 6, 12, 20]
    expect := some "(n + 1) * (n + 2)" },
  { name := "20d two names never multiply"
    input := "a(n) = n b", expect := some "n" }
]

def runCase (c : Case) : Result := Id.run do
  let custom := c.custom.map fun f =>
    if f.endsWith "2" then custom2 ((f.dropEnd 1).toString) else customAlt f
  let req : Request :=
    { input := c.input, names := c.names, types := c.types, custom
      values := c.values.toArray.mapIdx fun i v => (#[(i : Int)], v)
      verify := { engine := .internal, allowedFailures := c.allowed } }
  let r := analyze req
  let got := (r.items[0]?.map (·.body))
  let mut out := check c.name c.expect got
  if let some d := c.expectDecl then
    out := out ++ check (c.name ++ " (decl)") (some d) (r.items[0]?.map (·.decl))
  return out

end GenExprTests.Cases
