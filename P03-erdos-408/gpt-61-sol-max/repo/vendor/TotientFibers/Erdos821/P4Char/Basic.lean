module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import Erdos408.Graph.Kernel

public import Erdos821.Blueprint.Analytic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Erdos821.P4Char

open Blueprint.Analytic

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Finite character facts used by the cell-kernel supremum, reproduction,
and frame estimates. CharacterIndex uses levels 1 through Q, never zero.
Route for count: Fintype.card of DirichletCharacter at level r is totient r;
each level has at most Q characters. Route for norm: character values are
zero on nonunits and roots of unity on units. -/
def PrimitiveCharacterTask  :=
  (∀ Q : ℕ, (primitiveCharacters Q).card ≤ Q ^ 2) ∧
  (∀ (Q : ℕ) (χ : CharacterIndex Q) (n : ℕ), ‖charValue χ n‖ ≤ 1)



/-- Count part: the primitive characters at levels `1..Q` number at most `Q ^ 2`. -/
alias count_part := _root_.Erdos408.Graph.card_primitiveCharacters_le

/-- Norm part: every character value has norm at most one. -/
theorem norm_part :
    ∀ (Q : ℕ) (χ : CharacterIndex Q) (n : ℕ), ‖charValue χ n‖ ≤ 1 := fun Q χ n => DirichletCharacter.norm_le_one χ.snd ↑n

theorem PrimitiveCharacterTask_proof : PrimitiveCharacterTask :=
  ⟨count_part, norm_part⟩

end

end Erdos821.P4Char
