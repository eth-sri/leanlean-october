module

public import proofs.HordijkSteelThreshold.WordProtectedCore

@[expose] public section

namespace HordijkSteelThreshold
open Classical

theorem wordCut_core_avoiding_root {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (core : List Bool)
    (hc : ∀ e ∈ wordGraphCut f, ∃ l r : List Bool, e.1.val = l ++ core ++ r)
    (v : BoundedFoodWord L N)
    (hv : ¬ ∃ l r : List Bool, v.val = l ++ core ++ r) :
    f v = f (boundedFoodRoot L N) := by
  suffices ∀ k (u : BoundedFoodWord L N), foodWordHeight L u.val ≤ k →
      (¬ ∃ l r : List Bool, u.val = l ++ core ++ r) → f u = f (boundedFoodRoot L N) from
    this N v (by have := boundedFoodWord_length_le v; unfold foodWordHeight; omega) hv
  intro k; induction k with
  | zero => intro u hu _; rw [boundedFood_zero_height u (by omega)]
  | succ k ih =>
    intro u hu havoid
    by_cases hr : u = boundedFoodRoot L N
    · rw [hr]
    have heq : f u = f (boundedFoodRight u) := by
      by_contra hneq
      exact havoid (hc (u, true) (by simp [wordGraphCut, booleanEdgeCut, wordBasicEdges, wordEdgeParent, hr, hneq]))
    rw [heq]
    by_cases hp : boundedFoodRight u = boundedFoodRoot L N
    · rw [hp]
    have := foodWordRight_height L u.val
    refine ih _ (by change foodWordHeight L (foodWordRight L u.val) ≤ k; omega) ?_
    rintro ⟨l, r, hparent⟩
    obtain ⟨b, hb⟩ := boundedFoodRight_preimage u (boundedFoodRight u) hp rfl
    exact havoid ⟨l, r ++ [b], by simp [hb, hparent, List.append_assoc]⟩

theorem wordCut_nonfood_side_contains_core {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (core : List Bool)
    (hc : ∀ e ∈ wordGraphCut f, ∃ l r : List Bool, e.1.val = l ++ core ++ r)
    (v : BoundedFoodWord L N) (hv : f v ≠ f (boundedFoodRoot L N)) :
    ∃ l r : List Bool, v.val = l ++ core ++ r := by
  by_contra h
  exact hv (wordCut_core_avoiding_root f core hc v h)

end HordijkSteelThreshold
