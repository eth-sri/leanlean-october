module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureFubini
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureIntegrationByParts
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureDegree
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasurePositive
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureEndpoint
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasurePlaneScaling
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod

/-! # The degree-two stationary adjoint witness from the explicit Kolmogorov Gaussian -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/- The actual fundamental measure solves the stationary adjoint identity on punctured tests. -/
theorem bellmanFundamentalMeasure_stationary :
    IsBellmanStationaryAdjointPair bellmanFundamentalMeasure bellmanFundamentalMeasure := by
  intro φ hφ hc hs
  let fx : ℝ × ℝ → ℝ := fun q => q.2 * fderiv ℝ φ q (1, 0)
  let fv : ℝ × ℝ → ℝ := fun q =>
    fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) q (0, 1)
  have hcx : HasCompactSupport fx := (hc.fderiv_apply ℝ (1, 0)).mul_left
  have hcv : HasCompactSupport fv :=
    (hc.fderiv_apply ℝ (0, 1)).fderiv_apply ℝ (0, 1)
  have hx : Continuous fx := continuous_snd.mul
    (bellman_contDiff_direction hφ (1, 0)).continuous
  have hv : Continuous fv :=
    (bellman_contDiff_direction (bellman_contDiff_direction hφ (0, 1)) (0, 1)).continuous
  have hsx : tsupport fx ⊆ {q | q ≠ (0, 0)} :=
    tsupport_mul_subset_right.trans ((tsupport_fderiv_apply_subset ℝ (1, 0)).trans hs)
  have hsv : tsupport fv ⊆ {q | q ≠ (0, 0)} :=
    (tsupport_fderiv_apply_subset ℝ (0, 1)).trans
      ((tsupport_fderiv_apply_subset ℝ (0, 1)).trans hs)
  have hiX := bellman_integrable_fundamental_test hx hcx hsx
  have hiV := bellman_integrable_fundamental_test hv hcv hsv
  change (∫ q, fx q.val ∂bellmanFundamentalMeasure) +
    (∫ q, fv q.val ∂bellmanFundamentalMeasure) = 0
  rw [← integral_add hiX hiV]
  have _h_xinl_0 : (∫ q : BellmanPuncturedPlane, (fun q => fx q + fv q) q.val ∂bellmanFundamentalMeasure) =
      ∫ t : BellmanPositiveTime, (∫ q : ℝ × ℝ, bellmanGaussianKernel t q * (fun q => fx q + fv q) q)
        ∂bellmanPositiveTimeVolume := by
    let f := (fun q => fx q + fv q)
    have hf := (hx.add hv)
    have hc := (hcx.add hcv)
    have hs := ((tsupport_add fx fv).trans (union_subset hsx hsv))
    have he : MeasurableEmbedding (Subtype.val : BellmanPuncturedPlane → ℝ × ℝ) :=
      MeasurableEmbedding.subtype_coe isOpen_compl_singleton.measurableSet
    rw [bellmanFundamentalMeasure, integral_withDensity_eq_integral_toReal_smul
      measurable_bellmanFundamentalDensity
      (ae_of_all _ fun q => (bellmanFundamentalDensity_ne_top q).lt_top)]
    simp only [smul_eq_mul, bellmanFundamentalDensity_toReal, ← integral_mul_const]
    have _h_xinl_0 : Integrable (fun w : BellmanPositiveTime × BellmanPuncturedPlane => bellmanGaussianKernel w.1 w.2.val * f w.2.val) (bellmanPositiveTimeVolume.prod bellmanPuncturedVolume) := by
      have hcp := bellman_test_compact_subtype hc hs
      obtain ⟨a, ha, hb⟩ := bellmanPunctured_compact_lower_bound _ hcp
      have hfi : Integrable (fun q : BellmanPuncturedPlane => |f q.val|)
          bellmanPuncturedVolume :=
        ((hf.comp continuous_subtype_val).integrable_of_hasCompactSupport hcp).abs
      have hm : Measurable (fun w : BellmanPositiveTime × BellmanPuncturedPlane =>
          bellmanGaussianKernel w.1 w.2.val * f w.2.val) := by
        apply Continuous.measurable
        exact (continuous_bellmanGaussianKernel.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).mul
          (hf.comp (continuous_subtype_val.comp continuous_snd))
      refine ((integrable_bellmanTimeMajorant a).mul_prod hfi).mono'
        hm.aestronglyMeasurable (ae_of_all _ fun w => ?_)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (bellmanGaussianKernel_pos w.1 w.2.val)]
      by_cases hq : w.2 ∈ tsupport (fun q : BellmanPuncturedPlane => f q.val)
      · exact mul_le_mul_of_nonneg_right
          (bellmanGaussianKernel_le_timeMajorant a ha w.2.val (hb _ hq) w.1) (abs_nonneg _)
      · simp [image_eq_zero_of_notMem_tsupport hq]
    rw [integral_integral_swap
      (f := fun q : BellmanPuncturedPlane => fun t : BellmanPositiveTime =>
        bellmanGaussianKernel t q.val * f q.val)
      _h_xinl_0.swap]
    apply integral_congr_ae
    apply ae_of_all
    intro t
    dsimp only
    rw [← map_bellmanPuncturedVolume_coe, he.integral_map]
  rw [_h_xinl_0]
  have heq (t : BellmanPositiveTime) (q : ℝ × ℝ) :
      -q.2 * fderiv ℝ (bellmanGaussianKernel t) q (1, 0) +
        fderiv ℝ (fun z => fderiv ℝ (bellmanGaussianKernel t) z (0, 1)) q (0, 1) =
      bellmanGaussianTimeCoefficient t.val q * bellmanGaussianKernel t q := by
    rw [bellmanGaussianKernel_fderiv_position, bellmanGaussianKernel_fderiv_velocity_twice]
    dsimp [bellmanGaussianTimeCoefficient]
    field_simp [ne_of_gt t.property]
    ring
  change (∫ t : BellmanPositiveTime, (∫ q : ℝ × ℝ, bellmanGaussianKernel t q *
    (q.2 * fderiv ℝ φ q (1, 0) +
      fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) q (0, 1)))
    ∂bellmanPositiveTimeVolume) = 0
  simp_rw [bellmanGaussianKernel_integral_generator _ φ hφ hc, heq]
  exact bellmanGaussianTimeDerivative_integral_test_eq_zero hφ.continuous hc hs

/- The explicit Gaussian fundamental measure supplies the degree-two witness at every ratio. -/
theorem two_mem_bellmanAdmissibleDegrees (R ) (hR : 1 ≤ R) :
    (2 : ℝ) ∈ bellmanAdmissibleDegrees R := by
  rw [mem_bellmanAdmissibleDegrees_iff]
  refine ⟨bellmanFundamentalMeasure, bellmanFundamentalMeasure,
    bellmanFundamentalMeasure_radon, bellmanFundamentalMeasure_radon,
    Or.inl bellmanFundamentalMeasure_ne_zero, ?_, ?_,
    bellmanFundamentalMeasure_stationary, bellmanFundamentalMeasure_densityDegree,
    bellmanFundamentalMeasure_densityDegree⟩
  · simp
  · calc
      bellmanFundamentalMeasure = (1 : ENNReal) • bellmanFundamentalMeasure := by simp
      _ ≤ ENNReal.ofReal R • bellmanFundamentalMeasure := by
        gcongr
        simpa using ENNReal.ofReal_le_ofReal hR

end HypoellipticAleksandrov.KineticAleksandrov
