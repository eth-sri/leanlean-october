module

public import proofs.HordijkSteelThreshold.GatewayProbability

@[expose] public section

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory
open RAF RAF.Polymer RAF.Concrete















theorem revClosureStep_mono {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) {S T : Finset R} {A B : Finset M}
    (hST : S ⊆ T) (hAB : A ⊆ B) :
    revClosureStep Q S A ⊆ revClosureStep Q T B := by
  intro x hx
  simp only [revClosureStep, Finset.mem_union, Finset.mem_biUnion] at hx ⊢
  rcases hx with hxA | ⟨r, hrS, hx⟩
  · exact Or.inl (hAB hxA)
  · right
    refine ⟨r, hST hrS, ?_⟩
    rcases hx with hx | hx
    · by_cases hEnabled : RevEnabledLhs Q A r
      · have hEnabled' : RevEnabledLhs Q B r := fun y hy => hAB (hEnabled hy)
        simp [hEnabled] at hx
        simp [hEnabled', hx]
      · simp [hEnabled] at hx
    · by_cases hEnabled : RevEnabledRhs Q A r
      · have hEnabled' : RevEnabledRhs Q B r := fun y hy => hAB (hEnabled hy)
        simp [hEnabled] at hx
        simp [hEnabled', hx]
      · simp [hEnabled] at hx

theorem revClosureAt_mono_reactions {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) {S T : Finset R} (hST : S ⊆ T) :
    ∀ k, revClosureAt Q S k ⊆ revClosureAt Q T k := by
  intro k
  induction k with
  | zero => exact Finset.Subset.rfl
  | succ k ih =>
      exact revClosureStep_mono Q hST ih



end HordijkSteelThreshold
