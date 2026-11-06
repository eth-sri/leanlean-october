module

public meta import Init.Tactics

open Lean.Parser.Tactic

@[expose] public section

/-- Rewrite the goal, then close it from the local context. -/
macro "rwx" rws:rwRuleSeq : tactic => `(tactic| (rw $rws:rwRuleSeq; assumption))
