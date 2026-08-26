/-
Tokenizer for the plain-text math syntax used by OEIS `%F` lines (and close cousins).

The lexer normalizes common unicode lookalikes (`−`, `×`, `·`, superscripts, `√`) into their
ASCII forms, splits the input into tokens, and records two flags per token used by the grammar
to gate implicit multiplication: whether whitespace or junk separated it from its predecessor
(`2n` juxtaposes, `16 terms` does not). Identifiers starting with `_` (OEIS author names like
`_Paul Barry_`) are emitted as hard boundaries so trailing attributions never glue onto a
formula through a binary operator.

Everything works on character lists, avoiding the `String.Slice` pitfalls of this toolchain.
-/

import FormulaParser.Basic

namespace Formula

namespace Lex

inductive TokKind where
  | num
  | ident
  | lpar | rpar
  | lsq | rsq
  | lcurl | rcurl
  | comma | semi
  | eq
  | plus | minus | star | slash | caret | bang
  | dotDot
  /-- A summation introducer: `sum`, `Sum`, `Sigma`, `∑`. -/
  | sumKw
  /-- A product introducer: `prod`, `Product`, `∏`. -/
  | prodKw
  /-- An integral introducer: `integral`, `Integrate`, `∫`. -/
  | intKw
  /-- Recognized punctuation that can never participate in a formula (`<`, `|`, `_Name_`);
  acts as a hard boundary. -/
  | other

deriving instance BEq, Inhabited for TokKind

structure Tok where
  kind : TokKind
  txt : String
  /-- Character offset of the token start in the normalized input. -/
  pos : Nat := 0
  /-- Whitespace directly preceded this token (blocks implicit multiplication). -/
  wsBefore : Bool := false
  /-- Junk directly preceded this token (blocks implicit multiplication too). -/
  junkBefore : Bool := false
deriving Inhabited

deriving instance BEq for Tok

/-- Unicode normalization + ASCII expansions applied before tokenizing. -/
def normalizeChars (cs : List Char) : List Char :=
  cs.flatMap fun c =>
    match c with
    | '−' | '–' => ['-']
    | '×' | '·' | '∗' => ['*']
    | '⁰' => ['^', '0']
    | '¹' => ['^', '1']
    | '²' => ['^', '2']
    | '³' => ['^', '3']
    | '⁴' => ['^', '4']
    | '⁵' => ['^', '5']
    | '⁶' => ['^', '6']
    | '⁷' => ['^', '7']
    | '⁸' => ['^', '8']
    | '⁹' => ['^', '9']
    | '√' => ['s', 'q', 'r', 't']
    | _ => [c]

def isIdentStart (c : Char) : Bool := c.isAlpha ∨ c == '_'

def isIdentCont (c : Char) : Bool := c.isAlpha ∨ c.isDigit ∨ c == '_' ∨ c == '\''

private def keywordOf (w : String) : Option TokKind :=
  -- `sum_(…)` lexes as one identifier; strip trailing underscores before matching keywords.
  let base := String.ofList ((w.toLower.toList).reverse.dropWhile (· == '_')).reverse
  match base with
  | "sum" | "sigma" => some .sumKw
  | "prod" | "product" => some .prodKw
  | "integral" | "integrate" => some .intKw
  | _ => none

private def punctOf (c : Char) : Option TokKind :=
  match c with
  | '(' => some .lpar
  | ')' => some .rpar
  | '[' => some .lsq
  | ']' => some .rsq
  | '{' => some .lcurl
  | '}' => some .rcurl
  | ',' => some .comma
  | ';' => some .semi
  | '=' => some .eq
  | '+' => some .plus
  | '-' => some .minus
  | '*' => some .star
  | '/' => some .slash
  | '^' => some .caret
  | '!' => some .bang
  | '<' | '>' | '|' | '~' | ':' | '%' => some .other
  | _ => none

private def isDot (c : Char) : Bool := c == '.'

private def strToNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

/-- Digits with an optional single decimal fraction (`12`, `12.5`); `12..n` keeps both dots. -/
private def scanNum (cs : List Char) : String × List Char :=
  let (intPart, rest1) := spanDigits cs ""
  match rest1 with
  | '.' :: d :: rest2 =>
    if d.isDigit then
      let (frac, rest3) := spanDigits (d :: rest2) ""
      (intPart ++ "." ++ frac, rest3)
    else (intPart, rest1)
  | _ => (intPart, rest1)
where
  spanDigits : List Char → String → String × List Char
    | c :: rest, acc =>
      if c.isDigit then spanDigits rest (acc ++ String.singleton c) else (acc, c :: rest)
    | [], acc => (acc, [])

private def scanIdent (cs : List Char) : String × List Char :=
  goIdent cs []
where
  goIdent : List Char → List Char → String × List Char
    | c :: rest, acc =>
      if isIdentCont c then goIdent rest (c :: acc) else (String.ofList acc.reverse, c :: rest)
    | [], acc => (String.ofList acc.reverse, [])

/-- The tokenizer main loop; `ws`/`junk` describe what preceded the upcoming token.
Records here are kept on single lines: multi-line record literals do not parse inside
`partial def` bodies on this toolchain. -/
private partial def lexGo (chars : List Char) (pos : Nat) (ws junk : Bool) (acc : Array Tok) :
    Array Tok :=
  match chars with
  | [] => acc
  | c :: rest =>
    if c.isWhitespace then
      lexGo rest (pos + 1) true junk acc
    else if c.isDigit then
      let (txt, rest') := scanNum (c :: rest)
      let tok : Tok := { kind := .num, txt := txt, pos := pos, wsBefore := ws, junkBefore := junk }
      lexGo rest' (pos + txt.length) false false (acc.push tok)
    else if isIdentStart c then
      let (txt, rest') := scanIdent (c :: rest)
      -- `_Paul Barry_`-style names are prose markers, not math: hard boundaries.
      let kind : TokKind := if txt.startsWith "_" then .other else (keywordOf txt).getD .ident
      let tok : Tok := { kind := kind, txt := txt, pos := pos, wsBefore := ws, junkBefore := junk }
      lexGo rest' (pos + txt.length) false false (acc.push tok)
    else if c == '.' ∧ rest.any isDot then
      -- A `..` range separator. Decimals never get here: they start with a digit and their
      -- fraction is consumed by `scanNum`.
      match rest with
      | _ :: rest' =>
        let tok : Tok := { kind := .dotDot, txt := "..", pos := pos, wsBefore := ws, junkBefore := junk }
        lexGo rest' (pos + 2) false false (acc.push tok)
      | [] => lexGo rest (pos + 1) ws true acc
    else
      match punctOf c with
      | some kind =>
        let tok : Tok := { kind := kind, txt := String.ofList [c], pos := pos, wsBefore := ws, junkBefore := junk }
        lexGo rest (pos + 1) false false (acc.push tok)
      | none =>
        -- Unrecognized junk: hard boundary, skipped.
        lexGo rest (pos + 1) ws true acc

/-- Tokenize a raw input line. Junk characters are skipped but remembered via `junkBefore`. -/
def lex (input : String) : Array Tok :=
  lexGo (normalizeChars input.toList) 0 false false #[]

end Lex

end Formula
