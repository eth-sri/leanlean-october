import RequestProject.PresSubcomplex
import RequestProject.CombPi2RetractionSquares


/-! Literal cellular isomorphisms for a bijective change of generator
labels, with two-cell labels fixed. Pending final Lean verification. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb.PresGeneratorRelabel
universe u
variable {A B J : Type u} [DecidableEq A] [DecidableEq B]
  (e : A ≃ B) (ρ : J → FreeGroup A) (σ : J → FreeGroup B)
  (hrel : ∀ j, σ j = FreeGroup.map e (ρ j))

def forward :=
  presInclHom e e.injective ρ σ id hrel

omit [DecidableEq A] [DecidableEq B] in
include hrel in
theorem inverse_rel (j : J) : ρ j = FreeGroup.map e.symm (σ j) := by
  rw [hrel j, FreeGroup.map.comp]
  simp

def backward :=
  presInclHom e.symm e.symm.injective σ ρ id (inverse_rel e ρ σ hrel)


theorem backward_forward_E (x : A) :
    (backward e ρ σ hrel).onE ((forward e ρ σ hrel).onE x) = x :=
  e.symm_apply_apply x

