import GenExprTests
import GenExprTests.Cases

/-!
Entry point of `lake exe genexpr-test`.

The `#guard` suites already fail `lake build`; this runner exists to show the acceptance corpus
as one table, and to host cases that later need a runtime environment.

Usage: `lake exe genexpr-test [--filter SUBSTRING] [--list]`
-/

open GenExprTests

def main (args : List String) : IO UInt32 := do
  let filter? := match args with
    | "--filter" :: pat :: _ => some pat
    | _ => none
  let selected := Cases.corpus.filter fun c =>
    match filter? with
    | some p => (c.name.splitOn p).length > 1 || (c.input.splitOn p).length > 1
    | none => true
  if args.contains "--list" then
    for c in selected do IO.println s!"{c.name}  <-  {c.input}"
    return 0
  let results := selected.map Cases.runCase
  for (c, r) in Array.zip selected results do
    IO.println s!"{if r.isEmpty then "ok  " else "FAIL"} {c.name}"
  report "corpus" results
