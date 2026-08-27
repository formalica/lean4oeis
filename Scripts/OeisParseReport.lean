import FormulaParser.Parser
import Mathlib.Tactic
import Mathlib.Data.PNat.Defs
import SQLite

/-!
Parse-report over the first 10 sequences in `Metadata/oeis.db`: every `%F` line is fed
unchanged to `Formula.findFirst?` with target type `Nat → Int`, timed, and validated against
the sequence's known terms. No repo files are written; reports go to `/tmp/opencode`.

Run with:  lake env lean Scripts/OeisParseReport.lean
-/

set_option autoImplicit false

namespace OeisParseReport

open Lean Formula Lean.Elab.Term Lean.Elab.Command SQLite

/-- Number of leading known terms used for data validation. -/
def verifyCap : Nat := 8

structure Row where
  name : String
  offset : Int
  dataText : String
  formulasText : String

private def fetchRows : IO (Array Row) := do
  let db ← SQLite.«open» "Metadata/oeis.db" (busyTimeoutMs := 5000)
  let stmt ← db.prepare
    "SELECT name, \"offset\", data, all_unformalized_formulas_text \
     FROM sequence ORDER BY name LIMIT 100"
  let mut out := #[]
  while ← stmt.step do
    out := out.push
      { name := ← stmt.columnText 0
        offset := (← stmt.columnInt64 1).toInt
        dataText := ← stmt.columnText 2
        formulasText := ← stmt.columnText 3 }
  return out

private def jsonArr (s : String) : Array Json :=
  match Json.parse s with
  | .ok (.arr a) => a
  | _ => #[]

private def jsonStr (v : Json) : Option String :=
  match v with
  | .str s => some s
  | _ => none

/-- Leading terms that fit into `Int` (huge bignums truncate the list early). -/
private def intTerms (dataText : String) : List Int :=
  ((jsonArr dataText).toList.filterMap fun v =>
    match v with
    | .num _ => v.getInt?.toOption
    | _ => none).take verifyCap

/-- Shifts validation indices so they land in the `Nat` domain even for negative offsets. -/
private def effOffset (off : Int) (vals : List Int) : Nat × List Int :=
  if off < 0 then (0, vals.drop off.neg.toNat) else (off.toNat, vals)

/-- Compiler-evaluated data check (`native_decide`, since kernel `decide` gets stuck on
`Int.floor`/`Rat` routes): accepts `r` iff `(r (off + i)) == vals[i]` for all `i`. -/
private def dataVal (off : Nat) (vals : List Int) : Result → TermElabM Bool := fun r => do
  if vals.isEmpty then return false
  let pairs := ((List.range vals.length).map fun i =>
    s!"({toString (off + i)}, {vals[i]!})") |> String.intercalate ", "
  let all := s!"(List.all [{pairs}] (fun p => ({r.src} (p.1)) == p.2))"
  let chk := s!"(by native_decide : {all} = true)"
  try
    withoutModifyingState do
      let stx ← Elab.parseTermStr chk
      let _ ← withoutErrToSorry do elabTerm stx none
      synthesizeSyntheticMVars (postpone := .no)
      pure ()
    pure true
  catch _ => pure false

inductive LineStatus where
  | ok (src : String)
  | fail (reason : String)

private def processLine (raw : String) (off : Nat) (vals : List Int) :
    TermElabM (LineStatus × Nat) := do
  let t0 ← liftM IO.monoMsNow
  let res ← try
    let o ← findFirst? raw (.arr .nat .int) (dataVal off vals)
    pure (Sum.inl o)
  catch e =>
    pure (Sum.inr (← e.toMessageData.toString))
  let t1 ← liftM IO.monoMsNow
  let ms := t1 - t0
  match res with
  | .inl (some r) => pure (.ok r.src, ms)
  | .inl none => pure (.fail "no candidate validated", ms)
  | .inr err => pure (.fail s!"exception: {err}", ms)

private def escapeCell (s : String) : String :=
  (s.replace "|" "\\|").replace "\n" " "

/-- The whole run: reads the DB, tries every formula line, writes `/tmp/opencode`. -/
private def mainTerm : TermElabM Unit := do
  liftM <| IO.FS.createDirAll "/tmp/opencode"
  let rows ← liftM fetchRows
  let mdH ← liftM <| IO.FS.Handle.mk "/tmp/opencode/formula_parse_report_1000.md" .write
  let csvH ← liftM <| IO.FS.Handle.mk "/tmp/opencode/formula_parse_report_1000.csv" .write
  liftM <| csvH.putStrLn "name,line_index,status,time_ms,src_or_reason,formula"
  let mut totLines := 0
  let mut totOk := 0
  let mut totMs := 0
  for row in rows do
    let lines := (jsonArr row.formulasText).toList.filterMap jsonStr
    let vals0 := intTerms row.dataText
    let (off, vals) := effOffset row.offset vals0
    liftM <| mdH.putStrLn s!"\n## {row.name} (offset {row.offset}, {lines.length} formula lines, \
      verifying {vals.length} terms at n = {off}..{off + vals.length - 1})\n"
    liftM <| mdH.putStrLn "| # | status | time (ms) | parsed function | raw %F line |"
    liftM <| mdH.putStrLn "|---|---|---|---|---|"
    let mut idx := 0
    for raw in lines do
      let (status, ms) ← try
        processLine raw off vals
      catch e =>
        pure (.fail s!"harness exception: {← e.toMessageData.toString}", 0)
      totLines := totLines + 1
      totMs := totMs + ms
      let mut tag := "FAIL"
      let mut detail := "?"
      match status with
      | .ok src => totOk := totOk + 1; tag := "OK"; detail := src
      | .fail why => tag := "FAIL"; detail := why
      liftM <| mdH.putStrLn s!"| {idx} | {tag} | {ms} | `{escapeCell detail}` \
        | `{escapeCell raw}` |"
      liftM <| csvH.putStrLn s!"{row.name},{idx},{tag},{ms},\"{detail.replace "\"" "\"\""}\",\
        \"{raw.replace "\"" "\"\""}\""
      idx := idx + 1
  let summary := s!"sequences={rows.size} lines={totLines} ok={totOk} failed={totLines - totOk} \
    total_time_ms={totMs}"
  liftM <| mdH.putStrLn s!"\n# Summary\n\n{summary}\n"
  liftM <| mdH.flush
  liftM <| csvH.flush
  IO.println summary

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000000 in
run_cmd do
  liftTermElabM mainTerm

end OeisParseReport
