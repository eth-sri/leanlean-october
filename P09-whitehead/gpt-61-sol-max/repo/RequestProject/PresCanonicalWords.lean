import Mathlib.Tactic

import RequestProject.PresWordEmbedding
import RequestProject.PresSubcomplex

namespace FiniteChains.PresModel
variable {α β J K : Type u} [DecidableEq α] [DecidableEq β]

  (ρ : J → FreeGroup α)
  (a : α)
/-- Reduced words with a cancelling pair. Choosing a compatible generator makes
these nonempty representatives commute literally with generator embeddings. -/
def presCanonicalWords   (j : J)  :=
  (ρ j).toWord ++ [(a, true), (a, false)]

theorem presCanonicalWords_ne_nil   (j : J) :
    presCanonicalWords ρ a j ≠ [] := by
  simp [presCanonicalWords]

theorem presCanonicalWords_positive   (j : J) :
    0 < (presCanonicalWords ρ a j).length := by
  simp [presCanonicalWords]

theorem mk_presCanonicalWords   (j : J) :
    FreeGroup.mk (presCanonicalWords ρ a j) = ρ j := by
  have hc : FreeGroup.mk [(a, true), (a, false)] = (1 : FreeGroup α) := by
    change FreeGroup.of a * (FreeGroup.of a)⁻¹ = 1
    exact mul_inv_cancel _
  rw [presCanonicalWords, ← FreeGroup.mul_mk, hc, mul_one, FreeGroup.mk_toWord]

theorem presCanonicalWords_map  (σ : K → FreeGroup β)
    (f : α ↪ β) (g : J ↪ K) (h : ∀ j, σ (g j) = FreeGroup.map f (ρ j))
    (a : α) (j : J) :
    presCanonicalWords σ (f a) (g j) =
      (presCanonicalWords ρ a j).map (fun p => (f p.1, p.2)) := by
  grind [presCanonicalWords, FiniteChains.toWord_map]

/-- A labelled inclusion of group presentations now gives a literal word embedding,
with no independent compatibility assumption on the representatives. -/
def canonicalPresWordEmbedding  (σ : K → FreeGroup β)
    (f : α ↪ β) (g : J ↪ K) (h : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) (a : α) :
    PresWordEmbedding (presCanonicalWords ρ a) (presCanonicalWords σ (f a)) where
  gen := f
  cell := g
  word := presCanonicalWords_map ρ σ f g h a

end FiniteChains.PresModel
