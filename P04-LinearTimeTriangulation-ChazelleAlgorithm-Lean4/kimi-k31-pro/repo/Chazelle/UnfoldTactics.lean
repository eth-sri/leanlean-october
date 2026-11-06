module

public meta import Mathlib.Tactic

open Lean.Parser.Tactic

@[expose] public section

/-- Unfold definitions, then prove the result by `omega`. -/
macro "ufo" ids:(ppSpace colGt ident)+ loc:(location)? : tactic =>
  `(tactic| (unfold $ids:ident* $[$loc]?; omega))

/-- Unfold definitions, then normalize numerals. -/
macro "ufn" ids:(ppSpace colGt ident)+ loc:(location)? : tactic =>
  `(tactic| (unfold $ids:ident* $[$loc]?; norm_num))

/-- Unfold definitions, then simplify. -/
macro "ufs" ids:(ppSpace colGt ident)+ loc:(location)? : tactic =>
  `(tactic| (unfold $ids:ident* $[$loc]?; simp))

/-- Unfold definitions, then prove the result by `ring`. -/
macro "ufring" ids:(ppSpace colGt ident)+ loc:(location)? : tactic =>
  `(tactic| (unfold $ids:ident* $[$loc]?; ring))

/-- Unfold definitions, then decide the result. -/
macro "ufd" ids:(ppSpace colGt ident)+ loc:(location)? : tactic =>
  `(tactic| (unfold $ids:ident* $[$loc]?; decide))

/-- Unfold definitions, then prove the result by `linarith`. -/
macro "ufl" ids:(ppSpace colGt ident)+ loc:(location)? : tactic =>
  `(tactic| (unfold $ids:ident* $[$loc]?; linarith))

/-- Unfold definitions, then prove the result by `nlinarith`. -/
macro "ufnl" ids:(ppSpace colGt ident)+ loc:(location)? : tactic =>
  `(tactic| (unfold $ids:ident* $[$loc]?; nlinarith))

/-- Unfold definitions, then close by reflexivity. -/
macro "ufr" ids:(ppSpace colGt ident)+ loc:(location)? : tactic =>
  `(tactic| (unfold $ids:ident* $[$loc]?; rfl))
