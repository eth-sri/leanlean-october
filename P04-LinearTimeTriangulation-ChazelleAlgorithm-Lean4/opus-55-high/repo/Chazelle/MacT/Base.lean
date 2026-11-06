module

public import Chazelle.Spec

public section

open Lean in
macro "zn " xs:(ident term)+ : command => do
  let mut cs : Array Syntax := #[]
  for x in xs do
    cs := cs.push (← `(notation $(Syntax.mkStrLit x.raw[0].getId.toString):str => $(⟨x.raw[1]⟩)))
  return ⟨mkNullNode cs⟩

open Lean in
macro "zg " xs:(ident tacticSeq)+ : command => do
  let mut cs : Array Syntax := #[]
  for x in xs do
    let p : TSyntax `tactic := ⟨mkNode ``Lean.Parser.Tactic.paren #[mkAtom "(", x.raw[1], mkAtom ")"]⟩
    let q : TSyntax `Lean.Parser.Command.macroRhs :=
      ⟨mkNode ``Lean.Parser.Tactic.quot #[mkAtom "`(tactic|", p.raw, mkAtom ")"]⟩
    cs := cs.push (← `(macro $(Syntax.mkStrLit x.raw[0].getId.toString):str : tactic => $q))
  return ⟨mkNullNode cs⟩
