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

section
variable (T : ℝ)
    (hsmall : T * (highRowTotalMass R.rowMass / highCenterMix C) / historyReferenceRho (3^d) ≤
      1 / (2 + 8 * ((3^d : ℕ) : ℝ)^2))
include hsmall

theorem highUnionSource_priorBounds :
    HistoryPriorBounds (highNeighbors d k) (3^d) (highUnionLaw R (highCenterMix C))
      (highUnionActivation R (highCenterMix C)) T (highRowTotalMass R.rowMass / highCenterMix C) :=
  ⟨highNeighbors_degreeBound d k, one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3),
    highUnionActivation_measurable R G.activation_measurable _, highUnionSourceActivation_centered C R G hpos,
    div_nonneg G.total_positive.le (highCenterMix_mem C).1.le, highUnionSourceActivation_bound C R G hpos, hsmall⟩

/-- Structural response-summed packet annihilation implies the true
complete-union canonical mass pushforward is constant in time. -/
theorem highUnionSourceMass_prior_law_of_append_annihilation
    (hkill : ∀ j h S, MeasurableSet S →
      (∫ e, S.indicator (fun _ : ℝ => (1 : ℝ))
        (highUnionSourceMass C R (historyMarkedAppend
          (highNeighbors d k)
          (highNeighbors_symm d k) j (h,e))) *
        highUnionActivation R (highCenterMix C) e ∂highUnionLaw R (highCenterMix C)) = 0)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    Measure.map (highUnionSourceMass C R)
      (historyMarkedPrior (highNeighbors d k) (3^d) t
        (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))) =
    Measure.map (highUnionSourceMass C R)
      (historyMarkedReference (highNeighbors d k) (3^d)
        (highUnionLaw R (highCenterMix C))) := by
  letI := highUnionSourceLaw_probability C R G
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  exact historyMarkedPrior_invariant_law (highUnionSource_priorBounds C R G hpos T hsmall)
    _ (highUnionSourceMass_measurable C R G) hkill ht

end

end Generic

end NearlyMinimax
