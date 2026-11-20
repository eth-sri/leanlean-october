module

public meta import Lean

/-! A frame layout assigns consecutive local-variable numbers to its names.
List the names in calling-convention order, starting at the given slot. -/

public section

open Lean in
macro doc:(docComment)? "slots " n:num ids:(ppSpace colGt ident)+ : command => do
  let mut cmds := #[]
  for (x, i) in ids.zipIdx do
    let k := Syntax.mkNumLit (toString (n.getNat + i))
    cmds := cmds.push (← `(command| $[$doc]? abbrev $x : Nat := $k)).raw
  return ⟨mkNullNode cmds⟩
