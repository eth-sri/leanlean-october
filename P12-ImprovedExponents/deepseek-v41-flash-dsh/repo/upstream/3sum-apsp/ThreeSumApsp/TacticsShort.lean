/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Published under Apache 2.0 License.
-/
module

public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Abbreviations for one-line tactic proofs in terms

The proofs of the library close a side goal in the middle of a term with `(by omega)`,
`(by norm_num)` and their like. Each of these is one tactic, and its text is the same everywhere;
this file gives each the name of a term. `Nat.pow_le_pow_right hb (by omega)` is
`Nat.pow_le_pow_right hb tac_omega`.
-/

/-- `by omega`. -/
macro "tac_omega" : term => `(by omega)
/-- `by norm_num`. -/
macro "tac_norm_num" : term => `(by norm_num)
/-- `by positivity`. -/
macro "tac_positivity" : term => `(by positivity)
/-- `by linarith`. -/
macro "tac_linarith" : term => `(by linarith)
/-- `by simp`. -/
macro "tac_simp" : term => `(by simp)
/-- `by decide`. -/
macro "tac_decide" : term => `(by decide)
/-- `by ring`. -/
macro "tac_ring" : term => `(by ring)
/-- `by nlinarith`. -/
macro "tac_nlinarith" : term => `(by nlinarith)
/-- `by simp [...]`. -/
macro "tac_simp" "[" ss:Lean.Parser.Tactic.simpLemma,* "]" : term => `(by simp [$ss,*])
/-- `by rwa [...]`. -/
macro "tac_rwa" "[" ss:Lean.Parser.Tactic.rwRule,* "]" : term => `(by rwa [$ss,*])
