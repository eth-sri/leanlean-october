module

public meta import Init.Tactics
public meta import Mathlib.Tactic.SplitIfs
public meta import Mathlib.Tactic.FieldSimp
public meta import Lean.Elab.Tactic.NormCast
public meta import Mathlib.Tactic.Ring
public meta import Mathlib.Tactic.Linarith

@[expose] public section

/-- Split all if-then-else goals and close them by `omega`. -/
macro "splao" : tactic => `(tactic| (split_ifs <;> omega))

/-- Push casts, then prove the result by `ring`. -/
macro "pcr" : tactic => `(tactic| (push_cast; ring))

/-- Push casts, then prove the result by `linarith`. -/
macro "pcl" : tactic => `(tactic| (push_cast; linarith))

/-- Push casts, then prove the result by `nlinarith`. -/
macro "pcnl" : tactic => `(tactic| (push_cast; nlinarith))

/-- Clear field denominators, then prove the result by `ring`. -/
macro "fsr" : tactic => `(tactic| (field_simp; ring))

/-- Clear field denominators, then prove the result by `linarith`. -/
macro "fsl" : tactic => `(tactic| (field_simp; linarith))
