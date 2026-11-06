module

public import Lean
public meta import Lean.Elab.Tactic.Rewrite

@[expose] public section

namespace FiniteChains.Comb

universe u

/-- A list of oriented edges of type `E`. -/
abbrev Oriented (E : Type u) : Type u := List (E × Bool)

end FiniteChains.Comb

open Lean Meta Elab Parser Tactic
open Lean Elab Command

/-- Enable the backward-compatibility settings used by this project. -/
elab "backwardOptions" : command => do
  elabCommand (← `(command| set_option backward.defeqAttrib.useBackward true))
  elabCommand (← `(command| set_option backward.isDefEq.respectTransparency false))
  elabCommand (← `(command| set_option backward.isDefEq.respectTransparency.types false))

/-- Rewrite with default transparency, preserving the usual rule and location syntax. -/
macro "rwd" s:rwRuleSeq l:(location)? : tactic =>
  `(tactic| rw (config := { transparency := .default }) $s:rwRuleSeq $(l)?)

macro "rwd" s:rwRuleSeq : conv =>
  `(conv| rw (config := { transparency := .default }) $s:rwRuleSeq)
