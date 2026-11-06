module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureDensityScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasurePositive
import Mathlib.Tactic

/-! # The determinant factor for kinetic dilation of punctured-plane volume -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Product-plane Lebesgue measure has no point masses. -/
instance bellmanPlaneVolume_nullSingleton : NullSingletonClass (volume : Measure (ℝ × ℝ)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- Removing the origin does not change ambient Lebesgue measure. -/
theorem map_bellmanPuncturedVolume_coe :
    Measure.map (Subtype.val : BellmanPuncturedPlane → ℝ × ℝ) bellmanPuncturedVolume =
      volume := by
  have hm : MeasurableSet {q : ℝ × ℝ | q ≠ (0, 0)} :=
    isOpen_compl_singleton.measurableSet
  calc
    _ = volume.restrict _ := by
      convert! map_comap_subtype_coe hm volume using 1
    _ = _ := by
      apply Measure.restrict_eq_self_of_ae_mem
      apply ae_iff.mpr
      simp

variable (r : ℝ) (hr : 0 < r)

/-- The ambient dilation has determinant r to the fourth power. -/
theorem map_bellmanPlaneDilation_volume  (hr : 0 < r) :
    Measure.map (bellmanPlaneDilation r) (volume : Measure (ℝ × ℝ)) =
      ENNReal.ofReal (r⁻¹ ^ 4) • volume := by
  rw [Measure.volume_eq_prod]
  change Measure.map (Prod.map (fun x : ℝ => r ^ 3 * x) (fun v : ℝ => r * v))
    (volume.prod volume) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Real.map_volume_mul_left (pow_ne_zero 3 hr.ne'), Real.map_volume_mul_left hr.ne',
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  grind

/-- Positive kinetic dilation of the punctured plane is measurable. -/
theorem measurable_bellmanDilation  :
    Measurable (bellmanDilation r hr) := by
  apply Continuous.measurable
  unfold bellmanDilation
  fun_prop

/-- Punctured-plane volume has the same determinant scaling as ambient volume. -/
theorem map_bellmanPuncturedVolume_dilation  :
    Measure.map (bellmanDilation r hr) bellmanPuncturedVolume =
      ENNReal.ofReal (r⁻¹ ^ 4) • bellmanPuncturedVolume := by
  have he : MeasurableEmbedding (Subtype.val : BellmanPuncturedPlane → ℝ × ℝ) :=
    MeasurableEmbedding.subtype_coe isOpen_compl_singleton.measurableSet
  apply he.map_injective
  rw [Measure.map_map he.measurable (measurable_bellmanDilation r hr)]
  change Measure.map ((bellmanPlaneDilation r) ∘
    Subtype.val) bellmanPuncturedVolume = _
  rw [← Measure.map_map (by unfold bellmanPlaneDilation; fun_prop) he.measurable,
    map_bellmanPuncturedVolume_coe, map_bellmanPlaneDilation_volume r hr,
    Measure.map_smul _ he.measurable.aemeasurable, map_bellmanPuncturedVolume_coe]

end HypoellipticAleksandrov.KineticAleksandrov
