module

public meta import Mathlib.Tactic

open Lean.Parser.Tactic

@[expose] public section

/-- Rewrite, then prove the result by `omega`. -/
macro "rwo" rws:rwRuleSeq loc:(location)? : tactic =>
  `(tactic| (rw $rws:rwRuleSeq $(loc)?; omega))

/-- Rewrite, then simplify. -/
macro "rws" rws:rwRuleSeq loc:(location)? : tactic =>
  `(tactic| (rw $rws:rwRuleSeq $(loc)?; simp))

/-- Rewrite, then close by reflexivity. -/
macro "rwr" rws:rwRuleSeq loc:(location)? : tactic =>
  `(tactic| (rw $rws:rwRuleSeq $(loc)?; rfl))

/-- Rewrite, then prove the result by `ring`. -/
macro "rwring" rws:rwRuleSeq loc:(location)? : tactic =>
  `(tactic| (rw $rws:rwRuleSeq $(loc)?; ring))

/-- Rewrite, then prove the result by `linarith`. -/
macro "rwli" rws:rwRuleSeq loc:(location)? : tactic =>
  `(tactic| (rw $rws:rwRuleSeq $(loc)?; linarith))

/-- Rewrite, then prove the result by `nlinarith`. -/
macro "rwnl" rws:rwRuleSeq loc:(location)? : tactic =>
  `(tactic| (rw $rws:rwRuleSeq $(loc)?; nlinarith))

/-- Rewrite, then normalize numerals. -/
macro "rwn" rws:rwRuleSeq loc:(location)? : tactic =>
  `(tactic| (rw $rws:rwRuleSeq $(loc)?; norm_num))

/-- Rewrite, then decide the result. -/
macro "rwd" rws:rwRuleSeq loc:(location)? : tactic =>
  `(tactic| (rw $rws:rwRuleSeq $(loc)?; decide))
