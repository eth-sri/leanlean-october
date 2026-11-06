module

public meta import Mathlib.Tactic

open Lean.Parser.Tactic

@[expose] public section

/-- Simplify, then prove the result by `omega`. -/
macro "sio" rest:simpTraceArgsRest : tactic =>
  `(tactic| (simp? $rest:simpTraceArgsRest; omega))

/-- Simplify, then prove the result by `linarith`. -/
macro "sil" rest:simpTraceArgsRest : tactic =>
  `(tactic| (simp? $rest:simpTraceArgsRest; linarith))

/-- Simplify, then simplify again. -/
macro "sis" rest:simpTraceArgsRest : tactic =>
  `(tactic| (simp? $rest:simpTraceArgsRest; simp))

/-- Simplify, then prove the result by `ring`. -/
macro "sir" rest:simpTraceArgsRest : tactic =>
  `(tactic| (simp? $rest:simpTraceArgsRest; ring))

/-- Simplify, then normalize numerals. -/
macro "sin" rest:simpTraceArgsRest : tactic =>
  `(tactic| (simp? $rest:simpTraceArgsRest; norm_num))

/-- Simplify, then prove the result by `nlinarith`. -/
macro "sinl" rest:simpTraceArgsRest : tactic =>
  `(tactic| (simp? $rest:simpTraceArgsRest; nlinarith))

/-- Simplify, then close by reflexivity. -/
macro "sirfl" rest:simpTraceArgsRest : tactic =>
  `(tactic| (simp? $rest:simpTraceArgsRest; rfl))

/-- Simplify, then decide the result. -/
macro "sid" rest:simpTraceArgsRest : tactic =>
  `(tactic| (simp? $rest:simpTraceArgsRest; decide))
