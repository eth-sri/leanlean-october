module

public import NearlyMinimax.FinePairUnionMassAnnihilation
public import NearlyMinimax.HighUnionSourceConcentration
public import NearlyMinimax.HighHistoryInvariantMass

@[expose] public section

/-! Genuine complete-union source prior probability, invariant mass law,
and the original mass-power-tilted exceptional probability bound. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section Generic
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
    [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (R : HighUnionRowData d k F I E)
    {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
    (hpos : ∀ i, 0 < R.rowMass i)
include G hpos

theorem highUnionSourceActivation_bound (e : HighUnionMark E) :
    |highUnionActivation R (highCenterMix C) e| ≤
      highRowTotalMass R.rowMass / highCenterMix C :=
  highCenteredRowUnionActivation_bound R.rowMass hpos G.total_positive R.rowActivation
    G.activation_bound _ (highCenterMix_mem C).1 e

theorem highUnionSourceActivation_centered :
    (∫ e, highUnionActivation R (highCenterMix C) e ∂highUnionLaw R (highCenterMix C)) = 0 := by
  letI := G.row_probability
  exact highUnionActivation_centered R G.mass_nonneg G.activation_measurable
    (fun i => Integrable.of_bound (G.activation_measurable i).aestronglyMeasurable (R.rowMass i)
      (Filter.Eventually.of_forall (fun e => by simpa only [Real.norm_eq_abs] using G.activation_bound i e)))
    G.activation_centered _ (highCenterMix_mem C).1 (highCenterMix_mem C).2.le

/-- The actual complete tagged union, with its one corrective branch,
produces a genuine probability source path under the source positivity budget. -/
theorem highUnionSourcePrior_probability (T : ℝ) (hT : 0 ≤ T)
    (hsmall : T * (highRowTotalMass R.rowMass / highCenterMix C) / historyReferenceRho (3^d) ≤
      1 / (2 + 8 * ((3^d : ℕ) : ℝ)^2)) (t : ℝ) (ht : t ∈ Icc 0 T) :
    IsProbabilityMeasure (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t
      (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))) := by
  letI := highUnionSourceLaw_probability C R G
  have hm := highUnionActivation_measurable R G.activation_measurable (highCenterMix C)
  have hB : 0 ≤ highRowTotalMass R.rowMass / highCenterMix C :=
    div_nonneg G.total_positive.le (highCenterMix_mem C).1.le
  have hi : Integrable (highUnionActivation R (highCenterMix C))
      (highUnionLaw R (highCenterMix C)) :=
    Integrable.of_bound hm.aestronglyMeasurable _ (Filter.Eventually.of_forall fun e => by
      simpa only [Real.norm_eq_abs] using highUnionSourceActivation_bound C R G hpos e)
  have hs : t * (highRowTotalMass R.rowMass / highCenterMix C) / historyReferenceRho (3^d) ≤
      1 / (2 + 8 * ((3^d : ℕ) : ℝ)^2) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 hB)
      (historyReferenceRho_pos _).le).trans hsmall
  exact historyMarkedPrior_probability _ (highNeighborLabels_self_mem d k)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) (3^d)
    (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3)) (highNeighbor_dependency_card d k)
    t _ ht.1 hB _ _ hi (highUnionSourceActivation_centered C R G hpos)
    (highUnionSourceActivation_bound C R G hpos) hs

/-- Structural response-summed packet annihilation implies the true
complete-union canonical mass pushforward is constant in time. -/
theorem highUnionSourceMass_prior_law_of_append_annihilation (T : ℝ) (hT : 0 ≤ T)
    (hsmall : T * (highRowTotalMass R.rowMass / highCenterMix C) / historyReferenceRho (3^d) ≤
      1 / (2 + 8 * ((3^d : ℕ) : ℝ)^2))
    (hkill : ∀ j h S, MeasurableSet S →
      (∫ e, S.indicator (fun _ : ℝ => (1 : ℝ))
        (highUnionSourceMass C R (historyMarkedAppend
          (fun i j => j ∈ highNeighborLabels d k i)
          (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e))) *
        highUnionActivation R (highCenterMix C) e ∂highUnionLaw R (highCenterMix C)) = 0)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    Measure.map (highUnionSourceMass C R)
      (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t
        (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))) =
    Measure.map (highUnionSourceMass C R)
      (historyMarkedReference (fun i j => j ∈ highNeighborLabels d k i) (3^d)
        (highUnionLaw R (highCenterMix C))) := by
  letI := highUnionSourceLaw_probability C R G
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  exact historyMarkedPrior_invariant_law _ (highNeighborLabels_self_mem d k)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) (3^d)
    (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3)) (highNeighbor_dependency_card d k)
    T _ hT (div_nonneg G.total_positive.le (highCenterMix_mem C).1.le)
    (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))
    (highUnionActivation_measurable R G.activation_measurable _)
    (highUnionSourceActivation_centered C R G hpos) (highUnionSourceActivation_bound C R G hpos)
    hsmall _ (highUnionSourceMass_measurable C R G) hkill t ht

end Generic

section ActualFinePair
variable {d k D M q : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (Cfr T₀ N : ℝ)
    (hD : 3 ≤ D) (hq : 1 ≤ q) (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (hCfr : 1 ≤ Cfr) (hT₀ : 0 < T₀) (hTN : T₀ < N)
include hD hq hM hCfr hT₀ hTN

end ActualFinePair
end NearlyMinimax
