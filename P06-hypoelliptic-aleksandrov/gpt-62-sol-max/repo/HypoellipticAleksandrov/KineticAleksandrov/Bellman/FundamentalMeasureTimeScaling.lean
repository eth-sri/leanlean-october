module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureTime
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! # The positive-time change of variables for kinetic dilation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Positive scaling preserves the positive half-line and rescales its volume. -/
theorem map_positiveVolume_mul (s : ℝ) (hs : 0 < s) :
    Measure.map (fun t : ℝ => s * t) (volume.restrict (Ioi (0 : ℝ))) =
      ENNReal.ofReal s⁻¹ • volume.restrict (Ioi (0 : ℝ)) := by
  have hp : (fun t : ℝ => s * t) ⁻¹' Ioi (0 : ℝ) = Ioi 0 := by
    ext t
    exact mul_pos_iff_of_pos_left hs
  calc
    _ = (Measure.map (fun t : ℝ => s * t) volume).restrict (Ioi 0) := by
      rw [Measure.restrict_map (by fun_prop) measurableSet_Ioi, hp]
    _ = _ := by
      rw [Real.map_volume_mul_left hs.ne', Measure.restrict_smul,
        abs_of_pos (inv_pos.mpr hs)]

section
variable (r : ℝ) (hr : 0 < r)

/-- The positive-time scaling map is measurable. -/
theorem measurable_bellmanScaledTime :
    Measurable (bellmanScaledTime r hr) := by
  apply Continuous.measurable
  unfold bellmanScaledTime
  fun_prop

/-- Time volume scales by the inverse square of the kinetic dilation factor. -/
theorem map_bellmanPositiveTimeVolume_scaled :
    Measure.map (bellmanScaledTime r hr) bellmanPositiveTimeVolume =
      ENNReal.ofReal ((r ^ 2)⁻¹) • bellmanPositiveTimeVolume := by
  have hcoe : MeasurableEmbedding (Subtype.val : BellmanPositiveTime → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ioi
  apply hcoe.map_injective
  have hmap := Measure.map_map hcoe.measurable (measurable_bellmanScaledTime r hr)
    (μ := bellmanPositiveTimeVolume)
  rw [hmap]
  change Measure.map ((fun t : ℝ => r ^ 2 * t) ∘
      (Subtype.val : BellmanPositiveTime → ℝ)) bellmanPositiveTimeVolume = _
  rw [← Measure.map_map (by fun_prop) measurable_subtype_coe,
    map_bellmanPositiveTimeVolume_coe, map_positiveVolume_mul _ (pow_pos hr 2),
    Measure.map_smul _ hcoe.measurable.aemeasurable, map_bellmanPositiveTimeVolume_coe]

end

end HypoellipticAleksandrov.KineticAleksandrov
