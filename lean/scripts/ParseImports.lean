import Lean

/-! Read import headers with the same parser as Lean, without loading the imported modules. -/

def main (paths : List String) : IO Unit := do
  for path in paths do
    let (imports, _, messages) ← Lean.Elab.parseImports (← IO.FS.readFile path) (some path)
    if messages.hasErrors then
      for message in messages.toList do
        IO.eprintln (← message.toString)
      throw (IO.userError s!"cannot parse import header: {path}")
    -- Components preserve escaped identifiers containing dots or punctuation.
    let names := imports.map fun item =>
      item.module.components.map fun part => part.toString false
    IO.println (Lean.toJson (path, names)).compress
