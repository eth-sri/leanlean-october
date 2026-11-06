import Mathlib.Tactic

import RequestProject.PresSubcomplex
import RequestProject.CombPi2RetractionSquares

/-! Literal cellular isomorphisms for a bijective change of generator
labels, with two-cell labels fixed. Pending final Lean verification. -/

noncomputable section

namespace FiniteChains.Comb.PresGeneratorRelabel
variable {A B J : Type u} [DecidableEq A] [DecidableEq B]
  (e : A ≃ B) (ρ : J → FreeGroup A) (σ : J → FreeGroup B)
  (hrel : ∀ j, σ j = FreeGroup.map e (ρ j))

def forward  :=
  presInclHom e e.injective ρ σ id hrel

omit [DecidableEq A] [DecidableEq B] in
include hrel in
theorem inverse_rel (j : J) : ρ j = FreeGroup.map e.symm (σ j) := by simp_all [FreeGroup.map.comp]

def backward  :=
  presInclHom e.symm e.symm.injective σ ρ id (inverse_rel e ρ σ hrel)

abbrev backward_forward_V (x : (presComplex ρ).V)  :=
  Subsingleton.elim
    ((FiniteChains.Comb.PresGeneratorRelabel.backward e ρ σ hrel).onV
      ((FiniteChains.Comb.PresGeneratorRelabel.forward e ρ σ hrel).onV x))
    x

theorem backward_forward_E (x : A) :
    (backward e ρ σ hrel).onE ((forward e ρ σ hrel).onE x) = x :=
  e.symm_apply_apply x

theorem backward_forward_F (x : J) :
    (backward e ρ σ hrel).onF ((forward e ρ σ hrel).onF x) = x := rfl

end FiniteChains.Comb.PresGeneratorRelabel
