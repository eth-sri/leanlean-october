module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureTimeScaling
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasurePositive

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set


/-- The actual fundamental density has degree two under positive kinetic dilation. -/
theorem bellmanFundamentalDensity_dilation (r : ℝ) (hr : 0 < r)
    (q : BellmanPuncturedPlane) :
    bellmanFundamentalDensity (bellmanDilation r hr q) =
      ENNReal.ofReal (r⁻¹ ^ 2) * bellmanFundamentalDensity q  := by
  have bellmanFundamentalDensity_scaled_identity :
      ENNReal.ofReal ((r ^ 2)⁻¹) * bellmanFundamentalDensity (bellmanDilation r hr q) =
      ENNReal.ofReal (r⁻¹ ^ 4) * bellmanFundamentalDensity q := by
    have hf : Measurable (fun t => ENNReal.ofReal
        (bellmanGaussianKernel t (bellmanDilation r hr q).val)) :=
      ENNReal.measurable_ofReal.comp
        (continuous_bellmanGaussianKernel.comp
          (continuous_id.prodMk continuous_const)).measurable
    calc
      _ = ∫⁻ t, ENNReal.ofReal (bellmanGaussianKernel t (bellmanDilation r hr q).val)
          ∂(Measure.map (bellmanScaledTime r hr) bellmanPositiveTimeVolume) := by
        rw [map_bellmanPositiveTimeVolume_scaled, lintegral_smul_measure]
        rfl
      _ = ∫⁻ t, ENNReal.ofReal (bellmanGaussianKernel (bellmanScaledTime r hr t)
          (bellmanDilation r hr q).val) ∂bellmanPositiveTimeVolume :=
        lintegral_map hf (measurable_bellmanScaledTime r hr)
      _ = _ := by
        simp only [bellmanDilation_val, bellmanGaussianKernel_scaling,
          ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hr.le) 4)]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hc : ENNReal.ofReal (r ^ 2) * ENNReal.ofReal ((r ^ 2)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hr.le 2),
      mul_inv_cancel₀ (pow_ne_zero 2 hr.ne'), ENNReal.ofReal_one]
  have hp : ENNReal.ofReal (r ^ 2) * ENNReal.ofReal (r⁻¹ ^ 4) =
      ENNReal.ofReal (r⁻¹ ^ 2) := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hr.le 2)]
    congr 1
    field_simp
  calc
    _ = (ENNReal.ofReal (r ^ 2) * ENNReal.ofReal ((r ^ 2)⁻¹)) *
        bellmanFundamentalDensity (bellmanDilation r hr q) := by rw [hc, one_mul]
    _ = ENNReal.ofReal (r ^ 2) *
        (ENNReal.ofReal (r⁻¹ ^ 4) * bellmanFundamentalDensity q) := by
      rw [mul_assoc, bellmanFundamentalDensity_scaled_identity]
    _ = _ := by rw [← mul_assoc, hp]


/-- Product-plane Lebesgue measure has no point masses. -/
instance bellmanPlaneVolume_nullSingleton : NullSingletonClass (volume : Measure (ℝ × ℝ)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- Removing the origin does not change ambient Lebesgue measure. -/
theorem map_bellmanPuncturedVolume_coe :
    Measure.map (Subtype.val : BellmanPuncturedPlane → ℝ × ℝ) bellmanPuncturedVolume =
      volume := by
  unfold bellmanPuncturedVolume
  have hm : MeasurableSet {q : ℝ × ℝ | q ≠ (0, 0)} :=
    isOpen_compl_singleton.measurableSet
  calc
    _ = (volume : Measure (ℝ × ℝ)).restrict {q | q ≠ (0, 0)} := by
      convert! map_comap_subtype_coe hm volume using 1
    _ = _ := by
      apply Measure.restrict_eq_self_of_ae_mem
      apply ae_iff.mpr
      simpa using
        (measure_singleton (μ := (volume : Measure (ℝ × ℝ))) (0, 0))


/-- Positive kinetic dilation of the punctured plane is measurable. -/
theorem measurable_bellmanDilation (r : ℝ) (hr : 0 < r) :
    Measurable (bellmanDilation r hr) := by
  apply Continuous.measurable
  unfold bellmanDilation
  fun_prop

/-- Punctured-plane volume has the same determinant scaling as ambient volume. -/
theorem map_bellmanPuncturedVolume_dilation (r : ℝ) (hr : 0 < r) :
    Measure.map (bellmanDilation r hr) bellmanPuncturedVolume =
      ENNReal.ofReal (r⁻¹ ^ 4) • bellmanPuncturedVolume  := by
  have map_bellmanPlaneDilation_volume :
      Measure.map (bellmanPlaneDilation r) (volume : Measure (ℝ × ℝ)) =
      ENNReal.ofReal (r⁻¹ ^ 4) • volume := by
    rw [Measure.volume_eq_prod]
    change Measure.map (Prod.map (fun x => r ^ 3 * x) (fun v => r * v))
      ((volume : Measure ℝ).prod volume) = _
    rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
      Real.map_volume_mul_left (pow_ne_zero 3 hr.ne'), Real.map_volume_mul_left hr.ne',
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 2
    rw [abs_of_pos (inv_pos.mpr (pow_pos hr 3)), abs_of_pos (inv_pos.mpr hr)]
    ring
  have he : MeasurableEmbedding (Subtype.val : BellmanPuncturedPlane → ℝ × ℝ) :=
    MeasurableEmbedding.subtype_coe isOpen_compl_singleton.measurableSet
  apply he.map_injective
  rw [Measure.map_map he.measurable (measurable_bellmanDilation r hr)]
  change Measure.map ((bellmanPlaneDilation r) ∘
    (Subtype.val : BellmanPuncturedPlane → ℝ × ℝ)) bellmanPuncturedVolume = _
  rw [← Measure.map_map (by unfold bellmanPlaneDilation; fun_prop) he.measurable,
    map_bellmanPuncturedVolume_coe, map_bellmanPlaneDilation_volume,
    Measure.map_smul _ he.measurable.aemeasurable, map_bellmanPuncturedVolume_coe]

end HypoellipticAleksandrov.KineticAleksandrov

