module

public import proofs.HordijkSteelThreshold.GatewayProbability

public section

namespace HordijkSteelThreshold

open RAF RAF.Polymer RAF.Concrete

theorem revClosureStep_mono {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) {S T : Finset R} {A B : Finset M}
    (hST : S ⊆ T) (hAB : A ⊆ B) :
    revClosureStep Q S A ⊆ revClosureStep Q T B := by
  simp only [revClosureStep]
  grind [RevEnabledLhs, RevEnabledRhs]

theorem revClosureAt_mono_reactions {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) {S T : Finset R} (hST : S ⊆ T) :
    ∀ k, revClosureAt Q S k ⊆ revClosureAt Q T k
  | 0 => fun _ => id
  | k + 1 => revClosureStep_mono Q hST $ revClosureAt_mono_reactions Q hST k

end HordijkSteelThreshold
