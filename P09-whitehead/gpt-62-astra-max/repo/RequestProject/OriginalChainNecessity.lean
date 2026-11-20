module

public import RequestProject.ClassicalCWFixedPresentationComparison
public import RequestProject.PresTopologicalPerfectCover


@[expose] public section

/-! The original necessity direction, with one fixed presentation chosen
before any chain length or ambient CW complex. The result is an actual
regular topological cover of the original space. Unverified source. -/
noncomputable section
open scoped Classical
namespace Whitehead
open FiniteChains FiniteChains.ClassicalCW FiniteChains.PresModel

theorem hasAcyclicRegularCover_of_chains (K : TwoComplex)
    (h : ∀ n : ℕ, 1 ≤ n → HasChain K n false) : HasAcyclicRegularCover K := by
  let T := originalGraphTree K
  let w := fixedCanonicalWords K T
  let hpos :=
    fun j => List.length_pos_iff.mpr (fixedCanonicalWords_ne_nil K T j)
  let L := coveredPresentationTwoComplex w hpos
  have hL :=
    coveredPresentation_hasAcyclicRegularCover_of_presChains w hpos
      (fixedRelators K T) (fixedCanonicalWords_mk K T)
      (fixedPresChainsFS_of_original_chains K T h)
  let e : ContinuousMap.HomotopyEquiv K L := fixedCanonicalRealizationEquiv K T
  apply hasAcyclicRegularCover_of_homotopyEquiv <;> assumption

end Whitehead
