/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.SharedHyp

public import DOZZ.Correlations.Residue.FullSourceTailReduction
public import DOZZ.Correlations.SumTail.Reduction

/-! The joint-tail inequality `DOZZ.separatedSingularMass_joint_tail` and the two-insertion tail
`DOZZ.twoInsertion_tail_sum_uniform` supply the two-insertion hypothesis in both complete
residue-bridge reductions. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology
namespace DOZZ.Proofs

/-- The unit-volume residue bridge on its full domain (erratum K30, see
docs/ERRATA-AND-DEVIATIONS.md), with its literal one-insertion input as the only remaining tail
premise. -/
theorem residue_unitVolume_bridge_of_oneInsertion_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ α2 α3 : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : 0 < α2 ∧ α2 ≤ α3 ∧ γ / 2 < α3 ∧ α3 < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hone : OneInsertionHyp P X M γ) :
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ α3 (B α3) Z ∧
      Tendsto (fun ε : ℝ => ε * unitVolumeStructureConstant P M γ
          (α3 - α2 + ε) α2 α3) (𝓝[>] 0)
        (𝓝 (bridgeMultiplicity α2 α3 * reflectionExponent γ α3 *
          reflectionBarR P γ α3 (B α3) Z)) := by
  apply residue_unitVolume_bridge_of_insertion_tails P X M γ α2 α3 hγ hγ2 hα hX hM
  · exact hone
  · intro K2 K3 hK2 hK3 hpos2 hpos3 hsep A2 A3 hA2 hA3 hα2 hα3
      F2s F3s radius supBound derivBound lowerBound hF2 hF3
    exact sumtail_twoInsertion_tail_sum_uniform_of_oneInsertion_tail P X M γ hγ hγ2 hX hM
      K2 K3 hK2 hK3 hpos2 hpos3 hsep A2 A3 hA2 hA3 hα2 hα3
      F2s F3s radius supBound derivBound lowerBound hF2 hF3 hone

end DOZZ.Proofs
