
import Lean.Elab.Command

open Lean Elab Command

/-- `slots n a b c` declares `abbrev a : Nat := n`, `abbrev b : Nat := n + 1`, … (`n` defaults
to `0`). -/
syntax (docComment)? "slots " (num)? ident+ : command

elab_rules : command
  | `($[$d]? slots $[$n]? $xs*) => do
    let mut i := n.map (·.getNat) |>.getD 0
    for x in xs do
      elabCommand (← `($[$d]? abbrev $x : Nat := $(quote i)))
      i := i + 1
