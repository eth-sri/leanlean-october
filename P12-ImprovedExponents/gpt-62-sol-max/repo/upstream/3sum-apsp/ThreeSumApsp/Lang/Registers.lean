/-
Released under Apache 2.0 license, as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public meta import Lean

public section

open Lean

declare_syntax_cat lightRegister
syntax ident (" / " ident)* : lightRegister
syntax "_" : lightRegister

/-- Name consecutive locals starting at `from` (default zero). `_` reserves a slot, and
`a / b` gives the same slot two names, e.g. for an argument overwritten by the result. -/
syntax (docComment)? "registers" (" from " num)? " [" lightRegister,* "]" : command

macro_rules
  | `($[$doc:docComment]? registers $[from $start:num]? [$slots,*]) => do
    let mut i := start.map TSyntax.getNat |>.getD 0
    let mut cmds := #[]
    for slot in slots.getElems do
      if let `(lightRegister| $name:ident $[/ $aliases:ident]*) := slot then
        let index := Syntax.mkNumLit (toString i)
        for name in #[name] ++ aliases do
          let comment := if cmds.isEmpty then doc else none
          cmds := cmds.push (← `($[$comment:docComment]? abbrev $name : Nat := $index:num))
      i := i + 1
    pure (mkNullNode cmds)
