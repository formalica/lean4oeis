/-
Segmentation and grammar for the plain-text math syntax.

Given a noisy line ("From _Paul Barry_, Aug 19 2003: a(n) = Sum_{k=0..n} floor((k+4)/4)"),
this module locates the embedded formula(s):

1. tokenize (`Lex.lex`);
2. split into pieces at top-level `,`/`;` (bracket-depth aware);
3. per piece, optionally add a paren-repaired token variant (recovers missing `)`/`(`);
4. try parsing from *every* token position, keep each start's longest successful
   equality-chain, then pick the non-overlapping set with maximal total coverage (DP);
5. discard degenerate roots below `Config.minNodes`, canonicalize additive chains,
   deduplicate.

The grammar is a small precedence climber: additive < multiplicative (including gated
implicit multiplication) < unary minus < power (right-assoc) < factorial postfix < atoms,
plus dedicated forms for summation/product/integral binders.
-/

import FormulaParser.Ast
import FormulaParser.Lex

namespace Formula

namespace Grammar

open Lex

/-- Token index range carrying the equality-chain roots found there. -/
private structure Span where
  start : Nat
  stop : Nat
  roots : List Ast

private structure PCtx where
  toks : Array Tok
  cfg : Config

private def kindIs (toks : Array Tok) (i : Nat) (k : TokKind) : Bool :=
  match toks[i]? with
  | some t => t.kind == k
  | none => false

/-- Are we at the very end of the piece? Used to auto-close a trailing unclosed bracket. -/
private def atEnd (ctx : PCtx) (j : Nat) : Bool := j == ctx.toks.size

/-- Does a prose word follow (whitespace-separated identifier/punctuation)? A missing closing
bracket right before prose is recovered by auto-closing. -/
private def proseAhead (ctx : PCtx) (j : Nat) : Bool :=
  match ctx.toks[j]? with
  | some t => t.wsBefore ∧ (t.kind == .ident ∨ t.kind == .other)
  | none => false

private def canAutoClose (ctx : PCtx) (j : Nat) : Bool := atEnd ctx j ∨ proseAhead ctx j

/-- May `name` be parsed as a function call head? Registry-known names and single-letter
names yes; unknown multi-character names are prose (`blah (…`). -/
private def knownHead (cfg : Config) (name : String) : Bool :=
  name.length == 1 ∨ cfg.knownHeads.contains name ∨ cfg.knownHeads.contains name.toLower

private def strToNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

/-- Parse a numeral (integer or decimal) into a `Rat`. -/
private def strToRat (txt : String) : Rat :=
  match txt.splitOn "." with
  | [ip] => (strToNat ip : Rat)
  | [ip, fp] =>
    ((strToNat ip * 10 ^ fp.length + strToNat fp : Rat)) / (10 : Rat) ^ fp.length
  | _ => 0

/-- Binary operator precedence, or `none` when the token cannot continue an expression.
Boolean = right-associative. -/
private def binPrec : TokKind → Option (Nat × Bool)
  | .plus => some (1, false)
  | .minus => some (1, false)
  | .star => some (2, false)
  | .slash => some (2, false)
  | .caret => some (4, true)
  | _ => none

/-- Implicit multiplication gate: number-led juxtaposition with no whitespace/junk in
between (`2n`, `3a(n-1)`, `8(x+1)`). -/
private def canJuxtapose (left : Tok) (right : Tok) : Bool :=
  left.kind == .num ∧ (right.kind == .ident ∨ right.kind == .lpar)

/-! ### Precedence climber -/

mutual

/-- Expression at precedence `minPrec` starting at token index `i`. -/
private partial def parseExpr (ctx : PCtx) (fuel : Nat) (minPrec : Nat) (i : Nat) :
    Option (Ast × Nat) :=
  if fuel = 0 then none else
  match parseUnary ctx (fuel - 1) i with
  | none => none
  | some (l, j) => exprLoop ctx (fuel - 1) minPrec l j

/-- Consume binary operators while their precedence allows. The Bool triple is
`(precedence, rightAssoc, isImplicitMultiplication)`. -/
private partial def exprLoop (ctx : PCtx) (fuel : Nat) (minPrec : Nat) (acc : Ast) (j : Nat) :
    Option (Ast × Nat) :=
  if fuel = 0 then none else
  match ctx.toks[j]? with
  | none => some (acc, j)
  | some t =>
    let step : Option (Nat × Bool × Bool) :=
      match binPrec t.kind with
      | some (p, ra) => some (p, ra, false)
      | none =>
        if j > 0 then
          match ctx.toks[j - 1]? with
          | some prev =>
            if ctx.cfg.allowImplicitMul ∧ minPrec ≤ 2 ∧ canJuxtapose prev t ∧
                ¬t.wsBefore ∧ ¬t.junkBefore then some (2, false, true) else none
          | none => none
        else none
    match step with
    | none => some (acc, j)
    | some (p, ra, impl) =>
      if p < minPrec then some (acc, j) else
      let rhsAt := if impl then j else j + 1
      match parseExpr ctx (fuel - 1) (if ra then p else p + 1) rhsAt with
      | none =>
        -- operator without a right-hand side (trailing prose glued by `-` etc.): stop here
        some (acc, j)
      | some (r, j') =>
        let acc' :=
          if impl then .mul acc r
          else if t.kind == .plus then .add acc r
          else if t.kind == .minus then .sub acc r
          else if t.kind == .star then .mul acc r
          else if t.kind == .slash then .div acc r
          else .pow acc r -- caret
        exprLoop ctx (fuel - 1) minPrec acc' j'

private partial def parseUnary (ctx : PCtx) (fuel : Nat) (i : Nat) : Option (Ast × Nat) :=
  if fuel = 0 then none else
  if kindIs ctx.toks i .minus then
    match parseUnary ctx (fuel - 1) (i + 1) with
    | none => none
    | some (e, j) => some (.neg e, j)
  else
    parsePostfix ctx (fuel - 1) i

private partial def parsePostfix (ctx : PCtx) (fuel : Nat) (i : Nat) : Option (Ast × Nat) :=
  if fuel = 0 then none else
  match parsePrimary ctx (fuel - 1) i with
  | none => none
  | some (p, j) => postfixLoop ctx p j

private partial def postfixLoop (ctx : PCtx) (p : Ast) (j : Nat) : Option (Ast × Nat) :=
  if kindIs ctx.toks j .bang then postfixLoop ctx (.fact p) (j + 1) else some (p, j)

private partial def parsePrimary (ctx : PCtx) (fuel : Nat) (i : Nat) : Option (Ast × Nat) :=
  if fuel = 0 then none else
  match ctx.toks[i]? with
  | none => none
  | some t =>
    match t.kind with
    | .num => some (.lit (strToRat t.txt), i + 1)
    | .ident =>
      if kindIs ctx.toks (i + 1) .lpar ∧ knownHead ctx.cfg t.txt then
        match parseArgs ctx (fuel - 1) [] (i + 2) with
        | none => none
        | some (args, j) => some (.call t.txt args, j)
      else
        some (.sym t.txt, i + 1)
    | .lpar =>
      match parseExpr ctx (fuel - 1) 0 (i + 1) with
      | none => none
      | some (e, j) =>
        if kindIs ctx.toks j .rpar then some (e, j + 1)
        else if canAutoClose ctx j then some (e, j) -- recover missing `)`
        else none
    | .sumKw => parseBinder ctx (fuel - 1) i .sumI
    | .prodKw => parseBinder ctx (fuel - 1) i .prodI
    | .intKw => parseBinder ctx (fuel - 1) i .intI
    | _ => none

/-- Comma-separated call arguments starting at index `j`; returns past the closing `)`
(or at end-of-piece when it is missing). Arguments accumulate reversed in `acc`. -/
private partial def parseArgs (ctx : PCtx) (fuel : Nat) (acc : List Ast) (j : Nat) :
    Option (List Ast × Nat) :=
  if fuel = 0 then none else
  if kindIs ctx.toks j .rpar then some (acc.reverse, j + 1) else
  match parseExpr ctx (fuel - 1) 0 j with
  | none => none
  | some (a, k) =>
    if kindIs ctx.toks k .comma then parseArgs ctx (fuel - 1) (a :: acc) (k + 1)
    else if kindIs ctx.toks k .rpar then some ((a :: acc).reverse, k + 1)
    else if canAutoClose ctx k then some ((a :: acc).reverse, k) -- recover missing `)`
    else none

/-- Binder introducer forms. `j` points at the keyword. Accepted shapes:
`sum_(k=a)^b`, `sum_(k=a)^{b}`, `Sum_{k=a..b}`, `Sum_{k=a}^{b}`, `Σ_{k=a..b}`,
`integral(x=a)^b`, `Integral_{x=a..b}`, `∏_{k=a..b}`. An optional `_` between the keyword
and the bracket is skipped. Bare `∫_a^b` is rejected: no variable name can be recovered. -/
private partial def parseBinder (ctx : PCtx) (fuel : Nat) (j : Nat)
    (mk : String → Ast → Ast → Ast → Ast) : Option (Ast × Nat) :=
  if fuel = 0 then none else
  let i0 := j + 1
  let i1 :=
    match ctx.toks[i0]? with
    | some t => if t.kind == .ident ∧ t.txt == "_" then i0 + 1 else i0
    | none => i0
  if kindIs ctx.toks i1 .lpar then
    match parseVarEq ctx (fuel - 1) (i1 + 1) with
    | none => none
    | some (v, lo, i2) =>
      -- `sum_(k=a)^b`: the closing paren comes before the caret bound
      let i2' := if kindIs ctx.toks i2 .rpar then i2 + 1 else i2
      match caretBound ctx (fuel - 1) i2' with
      | none => none
      | some (hi, i3) => binderBody ctx (fuel - 1) mk v lo hi i3
  else if kindIs ctx.toks i1 .lcurl then
    match parseVarEq ctx (fuel - 1) (i1 + 1) with
    | none => none
    | some (v, lo, i2) =>
      if kindIs ctx.toks i2 .dotDot then
        match parseExpr ctx (fuel - 1) 5 (i2 + 1) with
        | none => none
        | some (hi, i3) =>
          if kindIs ctx.toks i3 .rcurl then binderBody ctx (fuel - 1) mk v lo hi (i3 + 1)
          else none
      else if kindIs ctx.toks i2 .rcurl then
        match caretBound ctx (fuel - 1) (i2 + 1) with
        | none => none
        | some (hi, i3) => binderBody ctx (fuel - 1) mk v lo hi i3
      else none
  else none

/-- `var = expr` up to (excluding) a closing paren/brace. -/
private partial def parseVarEq (ctx : PCtx) (fuel : Nat) (k : Nat) :
    Option (String × Ast × Nat) :=
  if fuel = 0 then none else
  match ctx.toks[k]? with
  | some t =>
    if t.kind == .ident ∧ kindIs ctx.toks (k + 1) .eq then
      match parseExpr ctx (fuel - 1) 0 (k + 2) with
      | none => none
      | some (lo, k') => some (t.txt, lo, k')
    else none
  | none => none

/-- Required `^{hi}` suffix; `hi` may be brace-wrapped or a prec-5 atom (`^n`, `^{n-1}`). -/
private partial def caretBound (ctx : PCtx) (fuel : Nat) (k : Nat) : Option (Ast × Nat) :=
  if fuel = 0 then none else
  if kindIs ctx.toks k .caret then
    if kindIs ctx.toks (k + 1) .lcurl then
      match parseExpr ctx (fuel - 1) 0 (k + 2) with
      | none => none
      | some (hi, k') => if kindIs ctx.toks k' .rcurl then some (hi, k' + 1) else none
    else
      parseExpr ctx (fuel - 1) 5 (k + 1)
  else none

/-- Parse the summation/product/integral body and build the node. -/
private partial def binderBody (ctx : PCtx) (fuel : Nat)
    (mk : String → Ast → Ast → Ast → Ast) (v : String) (lo hi : Ast) (k : Nat) :
    Option (Ast × Nat) :=
  if fuel = 0 then none else
  match parseExpr ctx (fuel - 1) 0 k with
  | none => none
  | some (body, k') => some (mk v lo hi body, k')

end

/-! ### Equality chains, spans and coverage -/

/-- Longest chain `expr (= expr)*` starting at index `i`; returns the segments. -/
private partial def parseChain (ctx : PCtx) (fuel : Nat) (i : Nat) : Option (List Ast × Nat) :=
  chainAux ctx fuel [] i
where
  /-- Segments accumulate reversed in `acc`. -/
  chainAux (ctx : PCtx) (fuel : Nat) (acc : List Ast) (i : Nat) :
      Option (List Ast × Nat) :=
    if fuel = 0 then none else
    match parseExpr ctx (fuel - 1) 0 i with
    | none =>
      match acc with
      | [] => none
      | _ => some (acc.reverse, i)
    | some (e, j) =>
      if kindIs ctx.toks j .eq then chainAux ctx (fuel - 1) (e :: acc) (j + 1)
      else some ((e :: acc).reverse, j)

/-- Can a formula start at this token kind? -/
private def isStarter : TokKind → Bool
  | .num | .ident | .lpar | .minus | .sumKw | .prodKw | .intKw => true
  | _ => false

/-- Longest chain parse from every viable start position. Spans whose every root sits below
`minNodes` are dropped before selection. -/
private def collectSpans (ctx : PCtx) (fuel : Nat) : Array Span :=
  (Array.range ctx.toks.size).filterMap fun s =>
    let starter :=
      match ctx.toks[s]? with
      | some t => isStarter t.kind
      | none => false
    if !starter then none else
      match parseChain ctx fuel s with
      | none => none
      | some (roots, e) =>
        let live := roots.any (fun r => r.size ≥ ctx.cfg.minNodes)
        if e > s ∧ live then some { start := s, stop := e, roots := roots } else none

/-- DP selection of non-overlapping spans maximizing total covered length, with QUADRATIC
weights so one long formula beats several fragments summing to the same length.
Deterministic (leftmost-longest among ties). -/
private partial def selectMaxCoverage (spans : Array Span) (n : Nat) : List Span :=
  let byStop := spans.mergeSort fun a b => a.stop < b.stop ∨ (a.stop == b.stop ∧ a.start < b.start)
  let best := dpFill byStop 1 (Array.replicate (n + 1) 0)
  backTrack byStop best n []
where
  weight (sp : Span) : Nat :=
    let l := sp.stop - sp.start
    l * l

  /-- Fill `best[i]` = maximal weight using tokens `< i`. -/
  dpFill (byStop : Array Span) (i : Nat) (best : Array Nat) : Array Nat :=
    if i ≥ best.size then best
    else
      let prev := best[i - 1]!
      let via := (byStop.filter (fun sp => sp.stop == i)).foldl (fun m sp =>
        max m (best[sp.start]! + weight sp)) prev
      dpFill byStop (i + 1) (best.set! i via)

  /-- Walk the DP table backwards collecting chosen spans. -/
  backTrack (byStop : Array Span) (best : Array Nat) (i : Nat) (acc : List Span) :
      List Span :=
    if i = 0 then acc
    else
      let keep : Option Span :=
        (byStop.filter (fun sp =>
          sp.stop == i ∧ best[sp.start]! + weight sp == best[i]!))[0]?
      match keep with
      | some sp => backTrack byStop best sp.start (sp :: acc)
      | none => backTrack byStop best (i - 1) acc

/-! ### Bracket recovery and piece splitting -/

/-- Round-bracket balance check: no closer without a preceding opener and none left over. -/
private partial def parenBalanced (ts : Array Tok) : Bool :=
  goB ts 0 0 0
where
  goB (ts : Array Tok) (i : Nat) (pa pc : Int) : Bool :=
    match ts[i]? with
    | none => pa == 0 ∧ pc ≥ 0
    | some t =>
      match t.kind with
      | .lpar => goB ts (i + 1) (pa + 1) pc
      | .rpar => if pa == 0 then false else goB ts (i + 1) (pa - 1) pc
      | .lsq | .lcurl => goB ts (i + 1) pa (pc + 1)
      | .rsq | .rcurl => goB ts (i + 1) pa (pc - 1)
      | _ => goB ts (i + 1) pa pc

/-- Shared scan: unmatched closers dropped, returning the surviving depth. -/
private partial def scanParensGo (ts : Array Tok) (i : Nat) (kept : Array Tok) (depth : Nat) :
    Nat × Array Tok :=
  match ts[i]? with
  | none => (depth, kept)
  | some t =>
    match t.kind with
    | .lpar => scanParensGo ts (i + 1) (kept.push t) (depth + 1)
    | .rpar => if depth = 0 then scanParensGo ts (i + 1) kept depth
               else scanParensGo ts (i + 1) (kept.push t) (depth - 1)
    | _ => scanParensGo ts (i + 1) (kept.push t) depth

/-- Remove right parens that never had an opener. -/
private def dropUnmatchedClosers (ts : Array Tok) : Array Tok :=
  (scanParensGo ts 0 #[] 0).2

private def parenExcess (ts : Array Tok) : Nat :=
  (scanParensGo ts 0 #[] 0).1

/-- Remove the last `excess` unmatched openers, scanning right to left. -/
private partial def dropOpenersGo (ts : Array Tok) (i need : Nat) (accRev : List Tok) :
    Array Tok :=
  if i = 0 then accRev.reverse.toArray
  else
    match ts[i - 1]? with
    | none => accRev.reverse.toArray
    | some t =>
      if need > 0 ∧ t.kind == .lpar then dropOpenersGo ts (i - 1) (need - 1) accRev
      else dropOpenersGo ts (i - 1) need (t :: accRev)

private def dropOpeners (ts : Array Tok) (excess : Nat) : Array Tok :=
  dropOpenersGo ts ts.size excess []

/-- Token arrays with unbalanced brackets repaired (unmatched closers and then openers
dropped); used as an extra recovery variant next to the original tokens. -/
private def balanceVariants (toks : Array Tok) : Array (Array Tok) :=
  if parenBalanced toks then #[toks]
  else
    let fixed := dropOpeners (dropUnmatchedClosers toks) (parenExcess toks)
    if fixed == toks then #[toks] else #[toks, fixed]

/-- Split tokens into pieces at `,`/`;` occurring at bracket depth zero. The separators are
dropped. -/
private partial def splitPieces (toks : Array Tok) : Array (Array Tok) :=
  goP toks 0 0 #[] #[]
where
  goP (ts : Array Tok) (i : Nat) (depth : Int) (cur : Array Tok) (out : Array (Array Tok)) :
      Array (Array Tok) :=
    match ts[i]? with
    | none => if cur.isEmpty then out else out.push cur
    | some t =>
      let d := match t.kind with
        | .lpar | .lsq | .lcurl => depth + 1
        | .rpar | .rsq | .rcurl => depth - 1
        | _ => depth
      if (t.kind == .comma ∨ t.kind == .semi) ∧ depth ≤ 0 then
        goP ts (i + 1) d #[] (if cur.isEmpty then out else out.push cur)
      else
        goP ts (i + 1) d (cur.push t) out

/-! ### Entry points -/

private def dedupAsts (as : List Ast) : List Ast :=
  as.foldl (fun acc a => if acc.any (fun b => b.render == a.render) then acc else acc ++ [a]) []

/-- All formula roots found in one token piece (already canonicalized, filtered, deduped).
Paren-repair variants are tried only when the original tokens yield nothing. -/
private def pieceRoots (cfg : Config) (fuel : Nat) (piece : Array Tok) : List Ast :=
  let rootsOf (toks : Array Tok) : List Ast :=
    (selectMaxCoverage (collectSpans { toks := toks, cfg := cfg } fuel) toks.size)
      |>.flatMap (·.roots)
  let main := rootsOf piece
  let raw : List Ast :=
    if !main.isEmpty then main
    else (balanceVariants piece).toList.flatMap fun v =>
      if v == piece then [] else rootsOf v
  dedupAsts ((raw.filter (fun a => a.size ≥ cfg.minNodes)).map Ast.canon)

/-- Find all formulas in a raw line. Returns canonicalized ASTs, best-first per piece,
pieces in order of appearance. `extraHeads` are additional surface names that may be parsed
as function-call heads (registry keys of the caller). -/
def parseLine (input : String) (cfg : Config := default) (extraHeads : List String := []) :
    List Ast :=
  let toks := Lex.lex input
  let fuel := 32 + 8 * toks.size
  let cfg' := { cfg with knownHeads := cfg.knownHeads ++ extraHeads }
  splitPieces toks |>.toList.flatMap (pieceRoots cfg' fuel)

end Grammar

end Formula
