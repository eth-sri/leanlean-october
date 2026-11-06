module

public meta import Chazelle.RewriteTactics
public meta import Chazelle.UnfoldTactics
public meta import Chazelle.SimpTactics

open Lean.Parser.Tactic

@[expose] public section

/-- Unfold, rewrite, then use `omega`. -/
macro "uro" ids:(ppSpace colGt ident)+ rws:rwRuleSeq : tactic =>
  `(tactic| (unfold $ids:ident*; rw $rws:rwRuleSeq; omega))

/-- Unfold, rewrite, then use reflexivity. -/
macro "urr" ids:(ppSpace colGt ident)+ rws:rwRuleSeq : tactic =>
  `(tactic| (unfold $ids:ident*; rw $rws:rwRuleSeq; rfl))

/-- Unfold, rewrite, then use `ring`. -/
macro "urring" ids:(ppSpace colGt ident)+ rws:rwRuleSeq : tactic =>
  `(tactic| (unfold $ids:ident*; rw $rws:rwRuleSeq; ring))

/-- Unfold, rewrite, then simplify. -/
macro "urs" ids:(ppSpace colGt ident)+ rws:rwRuleSeq : tactic =>
  `(tactic| (unfold $ids:ident*; rw $rws:rwRuleSeq; simp))

/-- Unfold, simplify, then use `omega`. -/
macro "usio" ids:(ppSpace colGt ident)+ rest:simpTraceArgsRest : tactic =>
  `(tactic| (unfold $ids:ident*; simp? $rest:simpTraceArgsRest; omega))

/-- Unfold, simplify, then use `ring`. -/
macro "usir" ids:(ppSpace colGt ident)+ rest:simpTraceArgsRest : tactic =>
  `(tactic| (unfold $ids:ident*; simp? $rest:simpTraceArgsRest; ring))

/-- Unfold, simplify, then use `linarith`. -/
macro "usil" ids:(ppSpace colGt ident)+ rest:simpTraceArgsRest : tactic =>
  `(tactic| (unfold $ids:ident*; simp? $rest:simpTraceArgsRest; linarith))

/-- Rewrite, unfold, then use `omega`. -/
macro "ruo" rws:rwRuleSeq ids:(ppSpace colGt ident)+ : tactic =>
  `(tactic| (rw $rws:rwRuleSeq; unfold $ids:ident*; omega))
macro "ruo" rws:rwRuleSeq ids:(ppSpace colGt ident)+ loc:location : tactic =>
  `(tactic| (rw $rws:rwRuleSeq; unfold $ids:ident* $loc:location; omega))

/-- Rewrite, simplify, then use `omega`. -/
macro "rsio" rws:rwRuleSeq rest:simpTraceArgsRest : tactic =>
  `(tactic| (rw $rws:rwRuleSeq; simp? $rest:simpTraceArgsRest; omega))
