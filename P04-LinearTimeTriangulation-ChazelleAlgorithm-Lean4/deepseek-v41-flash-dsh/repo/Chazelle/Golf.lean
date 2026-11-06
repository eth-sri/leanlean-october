module

public import Lean
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Short notations for common one-shot tactic proofs

Pure syntax abbreviations (`notation` / `macro`): they add nothing to the trusted base and
produce exactly the proof terms of the tactics they abbreviate.
`⋄` is `by omega`, `✓` is `by simp`, `Ρ h₁, h₂` is `by rw [h₁, h₂]`, `Ξ h₁, h₂` is the tactic
`rw [h₁, h₂]`, and so on.
-/

@[expose] public section

notation "⋄" => (by omega)
notation "✓" => (by simp)
notation "⌖" => (by decide)
notation "⊛" => (by norm_num)
notation "⟡" => (by linarith)
notation "⋆" => (by ring)
notation "⟢" => (by positivity)
notation "⊞" => (by nlinarith)
notation "⧫" => (by rfl)
notation "⟁" => (by assumption)

syntax "Ρ" Lean.Parser.Tactic.rwRule,* : term
macro_rules | `(Ρ $rules,*) => `(by rw [$rules,*])
syntax "⍟" Lean.Parser.Tactic.simpLemma,* : term
macro_rules | `(⍟ $lemms,*) => `(by simp only [$lemms,*])
syntax "⊚" Lean.Parser.Tactic.simpLemma,* : term
macro_rules | `(⊚ $lemms,*) => `(by simp [$lemms,*])

syntax "Ξ" Lean.Parser.Tactic.rwRule,* : tactic
macro_rules | `(tactic| Ξ $rules,*) => `(tactic| rw [$rules,*])
syntax "ϴ" Lean.Parser.Tactic.simpLemma,* : tactic
macro_rules | `(tactic| ϴ $lemms,*) => `(tactic| simp only [$lemms,*])
syntax "Θ" Lean.Parser.Tactic.simpLemma,* : tactic
macro_rules | `(tactic| Θ $lemms,*) => `(tactic| simp [$lemms,*])
syntax "Ξ'" Lean.Parser.Tactic.rwRule,* Lean.Parser.Tactic.location : tactic
macro_rules | `(tactic| Ξ' $rules,* $loc) => `(tactic| rw [$rules,*] $loc)
syntax "ϴ'" Lean.Parser.Tactic.simpLemma,* Lean.Parser.Tactic.location : tactic
macro_rules | `(tactic| ϴ' $lemms,* $loc) => `(tactic| simp only [$lemms,*] $loc)
syntax "Θ'" Lean.Parser.Tactic.simpLemma,* Lean.Parser.Tactic.location : tactic
macro_rules | `(tactic| Θ' $lemms,* $loc) => `(tactic| simp [$lemms,*] $loc)
