module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsConvolutionWindow

import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsConvolutionJets
import Mathlib.Analysis.Normed.Operator.Prod
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsLineWeak
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsParametric
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsConvolutionBounds
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsConvolutionRegularity

/-! # Actual C² regularity of position smoothing, including zero velocity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory Filter
open scoped Topology

/- Position smoothing is C² on the entire physical plane, without a regularity premise. -/
theorem positionBarrierConvolution_jet_spec {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (ha1 : alpha < 1)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ 2 κ) (hs : HasCompactSupport κ) :
    ∀ q0 : ℝ × ℝ,
      ContDiffAt ℝ 2 (positionBarrierConvolution κ phi) q0 ∧
      HasFDerivAt (positionBarrierConvolution κ phi) (∫ Y, barrierConvolutionJet κ phi q0 Y) q0 ∧
      HasFDerivAt (fun q => ∫ Y, barrierConvolutionJet κ phi q Y)
        (∫ Y, barrierConvolutionSecondJet κ phi q0 Y) q0 := by
  intro q0
  obtain ⟨R, hR, hwindow⟩ : ∃ R : ℝ, 0 < R ∧ ∀ q ∈ Metric.ball q0 1, ∀ Y : ℝ, Y ∉ Icc (-R) R →
      κ (q.1 - Y) = 0 ∧ deriv κ (q.1 - Y) = 0 ∧ deriv (deriv κ) (q.1 - Y) = 0 := by
    obtain ⟨S, hS, hSb⟩ := hs.isBounded.exists_pos_norm_lt
    let R := |q0.1| + S + 2
    refine ⟨R, by dsimp only [R]; positivity, fun q hq Y hY => ?_⟩
    have hqX := (barrier_parameter_ball_bounds hq).1
    have hn : q.1 - Y ∉ tsupport κ := by
      intro ht
      have hsmall := hSb (q.1 - Y) ht
      rw [Real.norm_eq_abs] at hsmall
      have hqabs : |q.1| ≤ |q0.1| + |q.1 - q0.1| := by
        calc |q.1| = |q0.1 + (q.1 - q0.1)| := by congr 1; ring
             _ ≤ _ := by simpa only [Real.norm_eq_abs] using norm_add_le q0.1 (q.1 - q0.1)
      have hYabs : |Y| ≤ |q.1| + |Y - q.1| := by
        calc |Y| = |q.1 + (Y - q.1)| := by congr 1; ring
             _ ≤ _ := by simpa only [Real.norm_eq_abs] using norm_add_le q.1 (Y - q.1)
      have hYlarge : R < |Y| := lt_of_not_ge (fun hh => hY (abs_le.mp hh))
      rw [abs_sub_comm Y q.1] at hYabs
      dsimp only [R] at hYlarge
      linarith only [hqabs, hqX, hYabs, hsmall, hYlarge]
    exact ⟨image_eq_zero_of_notMem_tsupport hn, deriv_of_notMem_tsupport hn,
      deriv_of_notMem_tsupport (fun hh => hn (tsupport_deriv_subset hh))⟩
  let K := Icc (-R) R
  let U := Metric.ball q0 1
  let mu := volume.restrict K
  have hmu : IsFiniteMeasure mu := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  let := hmu
  obtain ⟨K0, K1, K2, hK0, hK1, hK2, hbκ0, hbκ1, hbκ2⟩ :=
    barrier_kernel_uniform_bounds κ hκ hs
  obtain ⟨_, _, hv, hvv⟩ := h.origin_jet_bounds
  obtain ⟨Cv, hCv, hbv⟩ := hv
  obtain ⟨Cvv, hCvv, hbvv⟩ := hvv
  have hψ := h.origin_extension_continuous ha
  obtain ⟨B0, hB0b⟩ := ((isCompact_Icc (a := -R) (b := R)).prod
    (isCompact_Icc (a := q0.2 - 1) (b := q0.2 + 1))).exists_bound_of_continuousOn
      hψ.continuousOn
  let B := max B0 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbphi (q : ℝ × ℝ) (hq : q ∈ U) (Y : ℝ) (hY : Y ∈ K) :
      |bellmanOriginExtension phi (Y, q.2)| ≤ B := by
    have hqv := (barrier_parameter_ball_bounds hq).2
    have hv : q.2 ∈ Icc (q0.2 - 1) (q0.2 + 1) := by
      have hh := abs_lt.mp hqv
      constructor <;> linarith only [hh.1, hh.2]
    have hh := hB0b (Y, q.2) ⟨hY, hv⟩
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (le_max_left _ _)
  let p1 := (alpha - 1) / 3
  let p2 := (alpha - 2) / 3
  let b0 := fun _ : ℝ => K0 * B
  let b1 := fun Y : ℝ => K1 * B + K0 * Cv * |Y| ^ p1
  let b2 := fun Y : ℝ => K2 * B + 2 * K1 * Cv * |Y| ^ p1 + K0 * Cvv * |Y| ^ p2
  have hi1 : Integrable (fun Y : ℝ => |Y| ^ p1) mu :=
    (bellman_abs_rpow_locallyIntegrable p1 (by dsimp only [p1]; linarith))
      |>.integrableOn_isCompact isCompact_Icc
  have hi2 : Integrable (fun Y : ℝ => |Y| ^ p2) mu :=
    (bellman_abs_rpow_locallyIntegrable p2 (by dsimp only [p2]; linarith))
      |>.integrableOn_isCompact isCompact_Icc
  have hb0 : Integrable b0 mu := integrable_const _
  have hb1 : Integrable b1 mu := (integrable_const _).add (hi1.const_mul (K0 * Cv))
  have hb2 : Integrable b2 mu := ((integrable_const _).add
    (hi1.const_mul (2 * K1 * Cv))).add (hi2.const_mul (K0 * Cvv))
  let : TopologicalSpace.PseudoMetrizableSpace
      ((ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ)) := by
    let m : PseudoMetricSpace ((ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ)) := inferInstance
    exact ⟨⟨m.toUniformSpace, rfl, inferInstance⟩⟩
  have hmeas0 (q : ℝ × ℝ) : Measurable (barrierConvolutionIntegrand κ phi q) :=
    (hκ.continuous.measurable.comp (measurable_const.sub measurable_id)).mul
      (hψ.measurable.comp (measurable_id.prodMk measurable_const))
  have hmeas1 q := (barrierConvolutionJets_measurable h ha κ hκ q).1
  have hmeas2 q := (barrierConvolutionJets_measurable h ha κ hκ q).2
  have hae : ∀ᵐ Y ∂mu, Y ∈ K ∧ Y ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with Y hY hn
    exact ⟨hY, hn⟩
  have hs2 : ContDiffOn ℝ 2 (fun q => ∫ Y, barrierConvolutionIntegrand κ phi q Y ∂mu) U ∧
      (∀ q ∈ U, HasFDerivAt (fun p => ∫ Y, barrierConvolutionIntegrand κ phi p Y ∂mu)
        (∫ Y, barrierConvolutionJet κ phi q Y ∂mu) q) ∧
      (∀ q ∈ U, HasFDerivAt (fun p => ∫ Y, barrierConvolutionJet κ phi p Y ∂mu)
        (∫ Y, barrierConvolutionSecondJet κ phi q Y ∂mu) q) := by
    apply singular_parameter_integral_contDiffOn_two mu Metric.isOpen_ball
      (barrierConvolutionIntegrand κ phi) (barrierConvolutionJet κ phi)
      (barrierConvolutionSecondJet κ phi) b0 b1 b2 hb0 hb1 hb2
      (fun q _ => (hmeas0 q).aestronglyMeasurable)
      (fun q _ => (hmeas1 q).aestronglyMeasurable)
      (fun q _ => (hmeas2 q).aestronglyMeasurable)
    · filter_upwards [hae] with Y hY
      intro q hq
      rw [barrierConvolutionIntegrand, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hbκ0 _) (hbphi q hq Y hY.1) (abs_nonneg _) hK0
    · filter_upwards [hae] with Y hY
      intro q hq
      have hvb := barrier_position_fiber_bound (alpha - 1) (by linarith) _ Cv hCv hbv
        Y q.2 hY.2
      have _h_xinl_0 : ‖barrierConvolutionJet κ phi q Y‖ ≤
      |deriv κ (q.1 - Y)| * |bellmanOriginExtension phi (Y, q.2)| +
        |κ (q.1 - Y)| * |bellmanDv phi (Y, q.2)| := by
          simpa only [barrierConvolutionJet, abs_mul] using
            barrier_projection_norm_le
              (deriv κ (q.1 - Y) * bellmanOriginExtension phi (Y, q.2))
              (κ (q.1 - Y) * bellmanDv phi (Y, q.2))

        /- The second convolution jet needs only the locally integrable second velocity majorant. -/
      apply _h_xinl_0.trans
      dsimp only [b1, p1]
      calc
        _ ≤ K1 * B + K0 * (Cv * |Y| ^ ((alpha - 1) / 3)) := by
          gcongr
          all_goals first
          | exact hbκ1 _
          | exact hbphi q hq Y hY.1
          | exact hbκ0 _
        _ = _ := by ring
    · filter_upwards [hae] with Y hY
      intro q hq
      have hvb := barrier_position_fiber_bound (alpha - 1) (by linarith) _ Cv hCv hbv
        Y q.2 hY.2
      have hvvb := barrier_position_fiber_bound (alpha - 2) (by linarith) _ Cvv hCvv hbvv
        Y q.2 hY.2
      have _h_xinl_0 : ‖barrierConvolutionSecondJet κ phi q Y‖ ≤
      |deriv (deriv κ) (q.1 - Y)| * |bellmanOriginExtension phi (Y, q.2)| +
        2 * |deriv κ (q.1 - Y)| * |bellmanDv phi (Y, q.2)| +
          |κ (q.1 - Y)| * |bellmanDvv phi (Y, q.2)| := by
        unfold barrierConvolutionSecondJet
        have h1 := barrier_projection_norm_le
          (deriv (deriv κ) (q.1 - Y) * bellmanOriginExtension phi (Y, q.2))
          (deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2))
        have h2 := barrier_projection_norm_le
          (deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2))
          (κ (q.1 - Y) * bellmanDvv phi (Y, q.2))
        have hh := norm_add_le
          ((deriv (deriv κ) (q.1 - Y) * bellmanOriginExtension phi (Y, q.2)) •
            barrierPositionProjection + (deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2)) •
            barrierVelocityProjection |>.smulRight barrierPositionProjection)
          ((deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2)) • barrierPositionProjection +
            (κ (q.1 - Y) * bellmanDvv phi (Y, q.2)) • barrierVelocityProjection
              |>.smulRight barrierVelocityProjection)
        have hX : ‖barrierPositionProjection‖ = 1 := ContinuousLinearMap.norm_fst ℝ ℝ ℝ
        have hv : ‖barrierVelocityProjection‖ = 1 := ContinuousLinearMap.norm_snd ℝ ℝ ℝ
        simp only [ContinuousLinearMap.norm_smulRight_apply, hX, hv, mul_one] at hh
        simp only [abs_mul] at h1 h2
        linarith only [hh, h1, h2]
      apply _h_xinl_0.trans
      dsimp only [b2, p1, p2]
      calc
        _ ≤ K2 * B + 2 * K1 * (Cv * |Y| ^ ((alpha - 1) / 3)) +
            K0 * (Cvv * |Y| ^ ((alpha - 2) / 3)) := by
          gcongr
          all_goals first
          | exact hbκ2 _
          | exact hbphi q hq Y hY.1
          | exact hbκ1 _
          | exact hvb
          | exact hbκ0 _
        _ = _ := by ring
    · filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with Y hY
      intro q _
      have hk := ((hκ.differentiable (by norm_num) (q.1 - Y)).hasDerivAt).comp_hasFDerivAt q
        ((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).sub_const Y)
      have hh := hk.mul (barrier_slice_hasFDerivAt h q Y hY)
      convert hh using 1
      · rfl
      · apply ContinuousLinearMap.ext
        intro w
        simp [barrierConvolutionJet, barrierPositionProjection, barrierVelocityProjection]
        ring
    · filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with Y hY
      intro q _
      have hk := ((hκ.differentiable (by norm_num) (q.1 - Y)).hasDerivAt).comp_hasFDerivAt q
        ((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).sub_const Y)
      have hk' := ((hκ.differentiable_deriv_two (q.1 - Y)).hasDerivAt).comp_hasFDerivAt q
        ((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).sub_const Y)
      have hp := barrier_slice_hasFDerivAt h q Y hY
      have hp' : HasFDerivAt (fun p : ℝ × ℝ => bellmanDv phi (Y, p.2))
          (bellmanDvv phi (Y, q.2) • barrierVelocityProjection) q := by
          have hq : (Y, q.2) ∈ bellmanPuncturedSet := fun he => hY (congrArg Prod.fst he)
          have hd := ((h.directional_contDiffOn (0, 1)).contDiffAt
            (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt (by norm_num)
          exact (bellman_hasDerivAt_second hd).comp_hasFDerivAt q hasFDerivAt_snd

        /- The displayed first jet is the actual Fréchet derivative of the integrand. -/
      have hh := ((hk'.mul hp).smul_const barrierPositionProjection).add
        ((hk.mul hp').smul_const barrierVelocityProjection)
      convert hh using 1
      · rfl
      · apply ContinuousLinearMap.ext
        intro w
        apply ContinuousLinearMap.ext
        intro u
        simp [barrierConvolutionSecondJet, barrierPositionProjection, barrierVelocityProjection]
        ring
    · filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with Y hY
      have _h_xinl_0 : Continuous (fun q => barrierConvolutionSecondJet κ phi q Y) := by
        obtain ⟨hk1, hk2⟩ := barrier_kernel_derivatives_continuous κ hκ
        obtain ⟨hv, hvv⟩ : Continuous (fun q : ℝ × ℝ => bellmanDv phi (Y, q.2)) ∧
            Continuous (fun q : ℝ × ℝ => bellmanDvv phi (Y, q.2)) := by
            have hmap : MapsTo (fun q : ℝ × ℝ => (Y, q.2)) univ bellmanPuncturedSet :=
              fun _ _ he => hY (congrArg Prod.fst he)
            have hc : ContinuousOn (fun q : ℝ × ℝ => (Y, q.2)) univ :=
              (continuous_const.prodMk continuous_snd).continuousOn
            exact ⟨continuousOn_univ.mp ((h.directional_contDiffOn (0, 1)).continuousOn.comp hc hmap),
              continuousOn_univ.mp (h.dvv_continuousOn.comp hc hmap)⟩

          /- Scalar measurable coefficients give a measurable coordinate linear form. -/
        have hp : Continuous (fun q : ℝ × ℝ => bellmanOriginExtension phi (Y, q.2)) :=
          (h.origin_extension_continuous ha).comp (continuous_const.prodMk continuous_snd)
        have hk0 : Continuous (fun q : ℝ × ℝ => κ (q.1 - Y)) := hκ.continuous.comp (continuous_fst.sub
          continuous_const)
        have hk1' : Continuous (fun q : ℝ × ℝ => deriv κ (q.1 - Y)) := hk1.comp (continuous_fst.sub
          continuous_const)
        have hk2' : Continuous (fun q : ℝ × ℝ => deriv (deriv κ) (q.1 - Y)) := hk2.comp
          (continuous_fst.sub continuous_const)
        let LX := (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ((ℝ × ℝ) →L[ℝ] ℝ)).flip
          barrierPositionProjection
        let Lv := (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ((ℝ × ℝ) →L[ℝ] ℝ)).flip
          barrierVelocityProjection
        have h1 := barrier_projection_continuous (hk2'.mul hp) (hk1'.mul hv)
        have h2 := barrier_projection_continuous (hk1'.mul hv) (hk0.mul hvv)
        exact (LX.continuous.comp h1).add (Lv.continuous.comp h2)
      exact _h_xinl_0.continuousOn
  have he : positionBarrierConvolution κ phi =ᶠ[𝓝 q0]
      fun q => ∫ Y, barrierConvolutionIntegrand κ phi q Y ∂mu := by
    filter_upwards [Metric.ball_mem_nhds q0 (by norm_num : (0 : ℝ) < 1)] with q hq
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) ?_).symm
    intro Y hY
    rw [barrierConvolutionIntegrand, (hwindow q hq Y hY).1, zero_mul]
  have hq0 : q0 ∈ U := Metric.mem_ball_self (by norm_num)
  have he1 : (fun q => ∫ Y, barrierConvolutionJet κ phi q Y) =ᶠ[𝓝 q0]
      fun q => ∫ Y, barrierConvolutionJet κ phi q Y ∂mu := by
    filter_upwards [Metric.ball_mem_nhds q0 (by norm_num : (0 : ℝ) < 1)] with q hq
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) ?_).symm
    intro Y hY
    obtain ⟨h0, h1, _⟩ := hwindow q hq Y hY
    simp only [barrierConvolutionJet, h0, h1, zero_mul, zero_smul, add_zero]
  have he2 : (∫ Y, barrierConvolutionSecondJet κ phi q0 Y) =
      ∫ Y, barrierConvolutionSecondJet κ phi q0 Y ∂mu := by
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) ?_).symm
    intro Y hY
    obtain ⟨h0, h1, h2⟩ := hwindow q0 hq0 Y hY
    simp only [barrierConvolutionSecondJet, h0, h1, h2, zero_mul, zero_smul, add_zero,
      ContinuousLinearMap.zero_smulRight]
    apply ContinuousLinearMap.ext
    intro w
    apply ContinuousLinearMap.ext
    intro u
    simp only [add_apply, zero_apply, zero_add]
  have hcd := (hs2.1 q0 hq0).contDiffAt (Metric.ball_mem_nhds q0 (by norm_num))
  refine ⟨hcd.congr_of_eventuallyEq he, ?_, ?_⟩
  · rw [he1.eq_of_nhds]
    exact (hs2.2.1 q0 hq0).congr_of_eventuallyEq he
  · rw [he2]
    exact (hs2.2.2 q0 hq0).congr_of_eventuallyEq he1

/- Position smoothing is C² on the entire physical plane, including zero velocity. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
