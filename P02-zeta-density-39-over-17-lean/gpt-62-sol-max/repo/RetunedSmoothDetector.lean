module
public import RetunedDetectorParameters
public import MathCollab.Density.Stronger.SmoothDetector

@[expose] public section

open Real Complex MeasureTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density

/-- The actual contour detector is uniformly small for the stronger curve's
parameters. The Weyl input is proved and discharged; no moment is assumed. -/
theorem detector_eventually_small {σ a δ ε : ℝ}
    (hw : PhysicalDetectorWindow σ a) (hδ : δ ≤ 1/8) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      riemannZeta ρ = 0 →
      ‖smoothedDetector ρ (detectorX δ T) (1 / detectorY a T)‖ < ε := by
  obtain ⟨C, hC, hW⟩ := actual_zeta_weyl_input (by norm_num : (0 : ℝ) < 1/96)
  obtain ⟨A, hA, hbound⟩ := uniform_detector_integral_bound
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/96)).const_mul (A*C)
  simp only [mul_zero] at ht
  have hsmall : ∀ᶠ T : ℝ in atTop, A*C*T^(-1/48+1/96 : ℝ) < ε/2 := by
    have hexp : (-1/48+1/96 : ℝ) = -(1/96 : ℝ) := by norm_num
    rw [hexp]
    exact ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε/2))
  have hp := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).const_mul 72
  simp only [mul_zero] at hp
  have hpole : ∀ᶠ T : ℝ in atTop, 72*T^3*Real.exp (-T) < ε/2 := by
    simpa only [mul_zero, mul_assoc] using
      hp.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε/2))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall, hpole] with T hT hs hp
  intro ρ hβ hβ' hγ hγ' hzero
  have hTpos : 0 < T := by linarith
  have hX : 0 ≤ detectorX δ T := Real.rpow_nonneg hTpos.le _
  have hXT : detectorX δ T ≤ T := by
    simpa [detectorX] using Real.rpow_le_rpow_of_exponent_le hT
      (show δ ≤ 1 by linarith)
  have hY : 1 ≤ detectorY a T := Real.one_le_rpow hT (smoothingExponent_pos (by linarith [hw.a_low])).le
  have hYT : detectorY a T ≤ T := by
    simpa [detectorY] using Real.rpow_le_rpow_of_exponent_le hT
      (smoothingExponent_lt_one hw.a_high).le
  have hb : 3/4 ≤ ρ.re := hw.sigma_low.le.trans hβ
  have hi := hbound (1/6+1/96) C T (detectorX δ T) (detectorY a T) ρ
    (by norm_num) (by norm_num) hC.le hT hX (by linarith) hb hβ'.le hγ' hW
  have hscale := mul_le_mul_of_nonneg_left
    (detector_error_scale (η := 1/96) hw hδ hT hβ) (show 0 ≤ A*C by positivity)
  have hint : ‖detectorIntegral ρ (detectorX δ T) (detectorY a T)‖ < ε/2 :=
    (hi.trans (by simpa only [mul_assoc] using hscale)).trans_lt hs
  have hr := (norm_residue_le hT hX hXT hY hYT hb hβ'.le hγ hγ').trans_lt hp
  rw [smoothedDetector_contour_identity hY hb hβ' hzero]
  change ‖detectorResidue ρ (detectorX δ T) (detectorY a T) +
    detectorIntegral ρ (detectorX δ T) (detectorY a T)‖ < ε
  exact (norm_add_le _ _).trans_lt (by linarith)

/-- Uniform detection of every actual zero in the slab, with the exact new
parameters and the same ordinate. This does not yet choose a smooth dyadic block. -/
theorem detectorTail_eventually_large {σ a δ : ℝ}
    (hw : PhysicalDetectorWindow σ a) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/8) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      riemannZeta ρ = 0 →
      (1/2 : ℝ) ≤ ‖detectorTail ρ (detectorX δ T) (detectorY a T)‖ := by
  have hy : ∀ᶠ T : ℝ in atTop, 4 ≤ detectorY a T :=
    (tendsto_rpow_atTop (smoothingExponent_pos (by linarith [hw.a_low]))).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hy,
    detector_eventually_small hw hδ' (by norm_num : (0 : ℝ) < 1/4)] with T hT hY hs
  intro ρ hβ hβ' hγ hγ' hzero
  have hX : 1 ≤ detectorX δ T := Real.one_le_rpow hT hδ
  have hd := detectorTail_decomposition hX (show 0 < detectorY a T by linarith)
    (show 0 ≤ ρ.re by linarith [hw.sigma_low])
  have he : (3/4 : ℝ) ≤ Real.exp (-1 / detectorY a T) := by
    have hexp := Real.add_one_le_exp (-1 / detectorY a T)
    have hinv : 1 / detectorY a T ≤ (1/4 : ℝ) :=
      (div_le_iff₀ (by linarith : 0 < detectorY a T)).2 (by linarith)
    rw [neg_div] at hexp ⊢
    linarith
  have hn : ‖(Real.exp (-1 / detectorY a T) : ℂ)‖ ≤
      ‖smoothedDetector ρ (detectorX δ T) (1 / detectorY a T)‖ +
        ‖detectorTail ρ (detectorX δ T) (detectorY a T)‖ := by
    have hh : (Real.exp (-1 / detectorY a T) : ℂ) =
        smoothedDetector ρ (detectorX δ T) (1 / detectorY a T) -
          detectorTail ρ (detectorX δ T) (detectorY a T) := by rw [← hd]; ring
    rw [hh]
    exact norm_sub_le _ _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hn
  have hm := hs ρ hβ hβ' hγ hγ' hzero
  linarith



/-- All-zero smooth dyadic detection for the stronger parameters, with no
Weyl or moment premise. The finite list is chosen before rho varies. -/
theorem smoothDetector_eventually_large {σ a δ : ℝ}
    (hw : PhysicalDetectorWindow σ a) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/8) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      riemannZeta ρ = 0 →
      ∃ j ∈ smoothScaleIndices (detectorY a T*(Real.log T)^2),
        detectorX δ T/2 < (2 : ℝ)^j ∧
        (1/(24*Real.log T) : ℝ) ≤
          ‖smoothDetectorBlock ρ (detectorX δ T) (detectorY a T) j‖ := by
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 16,
    log_sq_eventually_le_height, detectorTail_eventually_large hw hδ hδ']
    with T hT hlog hlogSq hdetect
  intro ρ hβ hβ' hγ hγ' hzero
  have hTpos : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hX : 0 ≤ detectorX δ T := Real.rpow_nonneg hTpos.le _
  have hXT : detectorX δ T ≤ T := by
    simpa only [detectorX, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT1 (show δ ≤ 1 by linarith)
  have hY : 1 ≤ detectorY a T := Real.one_le_rpow hT1 (smoothingExponent_pos (by linarith [hw.a_low])).le
  have hYT : detectorY a T ≤ T := by
    simpa only [detectorY, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT1 (smoothingExponent_lt_one hw.a_high).le
  have hR : 1 ≤ detectorY a T*(Real.log T)^2 := by nlinarith
  have hRT : detectorY a T*(Real.log T)^2 ≤ T^2 := by
    calc
      _ ≤ T*T := mul_le_mul hYT hlogSq (sq_nonneg _) hTpos.le
      _ = _ := by ring
  have htail := smoothDetectorBlock_scale_tail_le_two_rpow hT1 hlog hX hXT hY hYT
    (show 0 ≤ ρ.re by linarith [hw.sigma_low])
  have hsmall : 2*T^(-2 : ℝ) ≤ (1/4 : ℝ) := by
    have he : 2*T^(-2 : ℝ) = 2/T^2 := by
      rw [Real.rpow_neg hTpos.le, Real.rpow_two]
      ring
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos hTpos)).mpr
    nlinarith
  obtain ⟨j, hj, hscale, hheight⟩ := exists_smoothDetectorBlock
    (show 0 < detectorY a T by linarith) (show 0 ≤ ρ.re by linarith [hw.sigma_low]) hR
    (by norm_num : (0 : ℝ) < 1/2) (hdetect ρ hβ hβ' hγ hγ' hzero)
    (by simpa only [show (1/2 : ℝ)/2 = 1/4 by norm_num] using htail.trans hsmall)
  refine ⟨j, hj, hscale, ?_⟩
  have hcard := smoothScaleIndices_card_le_log hT1 (by linarith) hR hRT
  have hcpos : (0 : ℝ) < (smoothScaleIndices (detectorY a T*(Real.log T)^2)).card := by
    exact_mod_cast Finset.card_pos.mpr (smoothScaleIndices_nonempty hR)
  calc
    (1/(24*Real.log T) : ℝ) ≤
        (1/2)/(2*(smoothScaleIndices (detectorY a T*(Real.log T)^2)).card) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      linarith
    _ ≤ _ := hheight

end Montgomery.RationalMoment.RightDetector
