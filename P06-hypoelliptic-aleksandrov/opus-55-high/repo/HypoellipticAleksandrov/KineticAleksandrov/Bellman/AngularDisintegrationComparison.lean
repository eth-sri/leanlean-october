module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationRepresentation
import Mathlib.Tactic

/-! # Comparison of the actual angular measures -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

variable (β : ℝ) {μ η : Measure BellmanPuncturedPlane}

/-- Pulling back through the angular embedding preserves measure comparison. -/
theorem bellmanAngularPullback_mono  (h : μ ≤ η) :
    bellmanAngularPullback μ ≤ bellmanAngularPullback η := by
  apply Measure.le_iff.mpr
  intro E hE
  rw [bellmanAngularPullback, bellmanAngularPullback,
    isOpenEmbedding_bellmanAngularPoint.measurableEmbedding.comap_apply,
    isOpenEmbedding_bellmanAngularPoint.measurableEmbedding.comap_apply]
  exact h _

/-- Weighting both compared measures by the same nonnegative density preserves comparison. -/
theorem bellman_withDensity_mono_measure {A : Type*} [MeasurableSpace A]
    {μ η : Measure A} (h : μ ≤ η) (f : A → ENNReal) :
    μ.withDensity f ≤ η.withDensity f := by
  apply Measure.le_iff.mpr
  intro E hE
  rw [withDensity_apply _ hE, withDensity_apply _ hE]
  exact lintegral_mono' (Measure.restrict_mono Subset.rfl h) le_rfl

/-- The canonical angular section preserves comparison of the original measures. -/
theorem bellmanAngularMeasure_mono  (h : μ ≤ η) :
    bellmanAngularMeasure β μ ≤ bellmanAngularMeasure β η := by
  have hp := bellman_withDensity_mono_measure (bellmanAngularPullback_mono h)
    (bellmanRadialDegreeWeight β)
  have hl := Measure.map_mono hp bellmanLogAngularHomeomorph.measurable
  have hs := Measure.map_mono
    (Measure.restrict_mono (s := Ioc (0) 1 ×ˢ univ) Subset.rfl hl) measurable_snd
  exact smul_le_smul_left _ hs

/-- Angular extraction commutes with multiplying the original measure by a scalar. -/
theorem bellmanAngularMeasure_smul  (c : ENNReal)
    (μ : Measure BellmanPuncturedPlane) :
    bellmanAngularMeasure β (c • μ) = c • bellmanAngularMeasure β μ := by
  unfold bellmanAngularMeasure bellmanUnitSection bellmanLogAngularMeasure
    bellmanAngularPullback
  rw [Measure.comap_smul, withDensity_smul_measure, Measure.map_smul,
    Measure.restrict_smul, Measure.map_smul, smul_comm]
  all_goals fun_prop

end HypoellipticAleksandrov.KineticAleksandrov
