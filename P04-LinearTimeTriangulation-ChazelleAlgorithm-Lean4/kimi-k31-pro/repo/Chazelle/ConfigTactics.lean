module

public meta import Chazelle.Programs.Tactics
public meta import Mathlib.Tactic

open Lean.Parser.Tactic

@[expose] public section

/-- Normalize configuration fields, then use `omega`. -/
macro "cso" : tactic => `(tactic| (config_simp; omega))
macro "cso" "at" h:ident : tactic => `(tactic| (config_simp at $h; omega))

/-- Normalize configuration fields, then simplify. -/
macro "css" : tactic => `(tactic| (config_simp; simp))
macro "css" "at" h:ident : tactic => `(tactic| (config_simp at $h; simp))

/-- Normalize configuration fields, then use reflexivity. -/
macro "csr" : tactic => `(tactic| (config_simp; rfl))
macro "csr" "at" h:ident : tactic => `(tactic| (config_simp at $h; rfl))

/-- Normalize configuration fields, then use `ring`. -/
macro "csring" : tactic => `(tactic| (config_simp; ring))
macro "csring" "at" h:ident : tactic => `(tactic| (config_simp at $h; ring))
