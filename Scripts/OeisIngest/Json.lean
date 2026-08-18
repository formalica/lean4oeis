/-!
Minimal JSON serialization helpers.

The ingest script only ever emits JSON *arrays of strings* (or of integer
numerals), so a full JSON library is not needed here.
-/

namespace Oeis.Json

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + (n - 10))

private def toHexAux : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | _ + 1, 0, acc => acc
  | fuel + 1, n, acc => toHexAux fuel (n / 16) (hexDigit (n % 16) :: acc)

/-- Renders `n` in lowercase hex, left-padded with `0` to at least `width` digits. -/
def toHex (n : Nat) (width : Nat := 0) : String :=
  let s := if n == 0 then "0" else String.ofList (toHexAux 128 n [])
  if s.length ≥ width then s else String.ofList (List.replicate (width - s.length) '0') ++ s

/-- Escapes a Lean string into the body of a JSON string literal. -/
def escape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | c => if c.toNat < 0x20 then acc ++ "\\u" ++ toHex c.toNat 4 else acc.push c

/-- A JSON string literal, quotes included. -/
def str (s : String) : String :=
  "\"" ++ escape s ++ "\""

/-- A JSON array of string literals. -/
def strArray (xs : Array String) : String :=
  "[" ++ String.intercalate "," (xs.toList.map str) ++ "]"

private def isIntegerLiteral (s : String) : Bool :=
  let body := if s.startsWith "-" then s.drop 1 else s
  !body.isEmpty && body.all Char.isDigit

/--
A JSON array of OEIS terms. Terms are emitted as bare (arbitrary precision)
numerals; anything that does not look like an integer is quoted instead so the
output stays valid JSON.
-/
def termArray (xs : Array String) : String :=
  "[" ++ String.intercalate "," (xs.toList.map fun x =>
    if isIntegerLiteral x then x else str x) ++ "]"

end Oeis.Json
