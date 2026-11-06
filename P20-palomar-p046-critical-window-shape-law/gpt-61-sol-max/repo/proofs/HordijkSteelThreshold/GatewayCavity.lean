
import proofs.HordijkSteelThreshold.GatewayProbability




namespace HordijkSteelThreshold

open RAF.Concrete















variable {M R : Type*}

variable [DecidableEq M] (Q : ReversibleCRS M R) {S T : Finset R}

theorem revClosureStep_mono   {A B : Finset M}
    (hST : S ⊆ T) (hAB : A ⊆ B) :
    revClosureStep Q S A ⊆ revClosureStep Q T B := by
  grind [revClosureStep, RevEnabledLhs, RevEnabledRhs]

theorem revClosureAt_mono_reactions   (hST : S ⊆ T) :
    ∀ k, revClosureAt Q S k ⊆ revClosureAt Q T k := by
  intro k
  induction k with
  | zero => exact Finset.Subset.rfl
  | succ k ih =>
      exact revClosureStep_mono Q hST ih



end HordijkSteelThreshold
