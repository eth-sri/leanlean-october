module

public import Chazelle.Machine.Structured

/-! # Postconditions of costed statements

`RunsWithin` is the usual upper-bound specification. `RunsFor` records an exact cost,
which is useful for straight-line blocks. Both expose the execution witness when composing
blocks and make the final configuration available in the postcondition. -/

@[expose] public section
namespace Chazelle.Machine

abbrev ExecPost (P : Polygon) (W : ℕ) (s : Stmt) (c : Config)
    (post : Config → ℕ → Prop) : Prop := ∃ d k, Exec P W s c d k ∧ post d k

abbrev RunsWithin (P : Polygon) (W : ℕ) (s : Stmt) (c : Config) (bound : ℕ)
    (post : Config → Prop) : Prop :=
  ExecPost P W s c fun d k => k ≤ bound ∧ post d

abbrev RunsFor (P : Polygon) (W : ℕ) (s : Stmt) (c : Config) (cost : ℕ)
    (post : Config → Prop) : Prop :=
  ExecPost P W s c fun d k => k = cost ∧ post d

end Chazelle.Machine
