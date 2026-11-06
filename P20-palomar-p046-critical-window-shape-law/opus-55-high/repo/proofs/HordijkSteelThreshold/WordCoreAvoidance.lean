module

public import proofs.HordijkSteelThreshold.WordProtectedCore

public section

namespace HordijkSteelThreshold
open Classical

variable {L N : ℕ} (f : BoundedFoodWord L N → Bool) (core : List Bool)

/-- A word avoiding the core of every boundary product lies on the food side.
Right truncation cannot cross such a boundary before reaching food. -/
theorem wordCut_core_avoiding_root
    (hc : ∀ e ∈ wordGraphCut f, ∃ l r : List Bool, e.1.val = l ++ core ++ r)
    (v : BoundedFoodWord L N)
    (hv : ¬ ∃ l r : List Bool, v.val = l ++ core ++ r) :
    f v = f (boundedFoodRoot L N) := by
  suffices ∀ k u, foodWordHeight L u.val ≤ k →
      (¬ ∃ l r : List Bool, u.val = l ++ core ++ r) →
      f u = f (boundedFoodRoot L N) by
    aesop
  intro k
  induction k with
  | zero =>
    intro u hu _
    rw [boundedFood_zero_height u $ by omega]
  | succ k ih =>
    intro u hu havoid
    by_cases hr : u = boundedFoodRoot L N
    · simp_all
    have heq : f u = f (boundedFoodRight u) := by
      by_contra hneq
      have he : (u, true) ∈ wordGraphCut f := by
        simp [wordGraphCut, booleanEdgeCut, wordBasicEdges, wordEdgeParent, hr, hneq]
      simp_all
    rw [heq]
    by_cases hp : boundedFoodRight u = boundedFoodRoot L N
    · simp_all
    have havp : ¬ ∃ l r : List Bool, (boundedFoodRight u).val = l ++ core ++ r := by
      obtain ⟨b, hb⟩ := boundedFoodRight_preimage u (boundedFoodRight u) hp rfl
      grind
    apply ih _ ?_ havp
    have hh := foodWordRight_height L u.val
    change foodWordHeight L (foodWordRight L u.val) ≤ k
    omega

/-- Consequently every molecule on the opposite side contains the protected core. -/
theorem wordCut_nonfood_side_contains_core
    (hc : ∀ e ∈ wordGraphCut f, ∃ l r : List Bool, e.1.val = l ++ core ++ r)
    (v : BoundedFoodWord L N) (hv : f v ≠ f (boundedFoodRoot L N)) :
    ∃ l r : List Bool, v.val = l ++ core ++ r := by
  by_contra h
  exact hv $ wordCut_core_avoiding_root f core hc v h

end HordijkSteelThreshold
