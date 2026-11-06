module

public import DOZZ.GMC.Moments.WeightedCutoffBallMomentUpToTwo

/-! # The weighted annulus estimate including the order one endpoint -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem cutoffWeightedGmcBallMoment_positive_scale_of_root_bound_ge_one
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    Xc (hXc : IsCircleAverage P X Xc)
    (γ α p : ℝ) (hγ : 0 < γ) (hα : 0 < α)
    (hp : 1 ≤ p)
    (hpRange : p < min (4 / γ ^ 2) (2 / γ * (Q γ - α)))
    ε (hε : 0 < ε)
    (hεbeta : ε ≤ weightedCutoffMomentScaleExponent γ α p / p)
    (A : ℝ≥0∞) (hA : A < ⊤)
    (hballRoot : ∀ (z : ℂ) (R δ : ℝ),
      0 < R → R ≤ 1 / 2 → 0 < δ → δ ≤ R → ‖z‖ + 2 * R ≤ 1 →
      (((∫⁻ ω, ENNReal.rpow
        (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) ^
          (1 / p) ≤ A * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^
            ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p))) ∧
        (∫⁻ ω, ENNReal.rpow
          (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) < ⊤)) :
    cutoffWeightedPositiveScaleRootBoundConstant A γ p ε ^ p < ⊤ ∧
      ∀ z : ℂ, ∀ R : ℝ,
      0 < R → R ≤ 1 / 2 → ‖z‖ + 2 * R ≤ 1 →
      ∀ δ : ℝ, 0 < δ → δ ≤ R →
      (∫⁻ ω, ENNReal.rpow
        (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P) ≤
        cutoffWeightedPositiveScaleRootBoundConstant A γ p ε ^ p * ENNReal.ofReal
          (R ^ weightedCutoffMomentScaleExponent γ α p) := by
  classical
  have hp0 := lt_of_lt_of_le zero_lt_one hp
  let xi := 2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2
  let beta := weightedCutoffMomentScaleExponent γ α p / p
  have hbeta := div_pos (weightedGmcMomentExponent_pos_of_sharp_range hγ hp0 hpRange) hp0
  let halfRatioReal := (1 / 2 : ℝ) ^ beta
  let halfRatio := ENNReal.ofReal halfRatioReal
  let halfRatio0Real := (1 / 2 : ℝ) ^ ε
  let halfRatio0 := ENNReal.ofReal halfRatio0Real
  let coreCoefReal := ((1 / 8 : ℝ)⁻¹) ^ (xi / p)
  let shellCoefReal := (2 / (1 / 8 : ℝ)) ^ (xi / p)
  have hratio : halfRatio ≤ halfRatio0 := ENNReal.ofReal_le_ofReal (by dsimp [halfRatioReal, halfRatio0Real]; exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by simpa [beta] using hεbeta))
  have hcoreCoefPos : 0 < coreCoefReal := by
    dsimp [coreCoefReal]
    exact Real.rpow_pos_of_pos (by norm_num) _
  let D := ENNReal.ofReal coreCoefReal +
    ENNReal.ofReal shellCoefReal * halfRatio0 * (1 - halfRatio0)⁻¹
  let K := A * D
  have hK : K < ⊤ := by
    dsimp [K]
    exact ENNReal.mul_lt_top hA (by dsimp [D]; exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) (lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr (by intro h; exact (not_le_of_gt (ENNReal.ofReal_lt_one.mpr (by simpa [halfRatio0] using (by dsimp [halfRatio0Real]; exact Real.rpow_lt_one (by norm_num) (by norm_num) hε)))) (tsub_eq_zero_iff_le.mp h))))⟩)
  have hKeq : K = cutoffWeightedPositiveScaleRootBoundConstant A γ p ε := by
    simp [K, D, cutoffWeightedPositiveScaleRootBoundConstant, coreCoefReal,
      shellCoefReal, halfRatio0, halfRatio0Real, xi]
  refine ⟨?_, ?_⟩
  · rw [← hKeq]
    exact lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg hp0.le hK.ne)
  · intro z R hR hRsmall hchart δ hδ hδR
    obtain ⟨N, hNlo, hNhi⟩ : ∃ N : ℕ,
        cutoffDyadicBallRadius R (N + 1) ≤ δ ∧ δ ≤ cutoffDyadicBallRadius R N := by
      by_cases hδeq : δ = R
      · refine ⟨0, ?_, ?_⟩
        · have hRhalf : R / 2 ≤ R := by
            apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
            linarith only [hR]
          simpa [cutoffDyadicBallRadius, hδeq] using hRhalf
        · rw [hδeq]
          simp [cutoffDyadicBallRadius]
      · have hδlt : δ < R := lt_of_le_of_ne hδR hδeq
        obtain ⟨N, hlow, hhigh⟩ := exists_dyadic_shell_index hδ hδlt
        exact ⟨N, hlow, hhigh.le⟩
    have hcoreBase := hballRoot z δ δ hδ (le_trans hδR hRsmall) hδ le_rfl (by linarith only [hchart, hδR])
    let coreMass : Ω → ℝ≥0∞ := fun ω =>
      regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z δ)
    let coreCoeff := ENNReal.ofReal (δ ^ (-γ * α))
    have hcoreRoot :
        (∫⁻ ω, (coreCoeff * coreMass ω) ^ p ∂P) ^ (1 / p) ≤
          A * ENNReal.ofReal coreCoefReal * ENNReal.ofReal (R ^ beta) := by
      calc
        _ = coreCoeff * (∫⁻ ω, ENNReal.rpow (coreMass ω) p ∂P) ^ (1 / p) := (ennreal_lintegral_rpow_const_mul_root_eq p hp0 coreCoeff ENNReal.ofReal_lt_top coreMass (by exact regularizedGMC_mass_aemeasurable P X hX Xc hXc γ (Real.log (1 / δ)) (Metric.ball z δ) Metric.isOpen_ball.measurableSet) hcoreBase.2)
        _ ≤ coreCoeff * (A * ENNReal.ofReal ((δ / (1 / 8 : ℝ)) ^ (xi / p))) :=
          mul_le_mul_of_nonneg_left hcoreBase.1 (by positivity)
        _ = A * (coreCoeff * ENNReal.ofReal
            ((δ / (1 / 8 : ℝ)) ^ (xi / p))) := by ac_rfl
        _ ≤ A * ENNReal.ofReal (coreCoefReal * R ^ beta) :=
          mul_le_mul_of_nonneg_left (by rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]; exact ENNReal.ofReal_le_ofReal (by rw [(show δ ^ (-γ * α) * (δ / (1 / 8 : ℝ)) ^ (xi / p) = coreCoefReal * δ ^ beta by simpa [xi, beta, coreCoefReal] using (weighted_cutoff_core_rpow_identity γ α p δ hγ hp0 hδ))]; exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ.le hδR hbeta.le) (le_of_lt hcoreCoefPos))) (by positivity)
        _ = A * ENNReal.ofReal coreCoefReal * ENNReal.ofReal (R ^ beta) := by
          rw [ENNReal.ofReal_mul (le_of_lt hcoreCoefPos)]
          ac_rfl
    let shellMass (n : ℕ) (ω : Ω) := regularizedGMC P Xc γ (Real.log (1 / δ)) ω
        (Metric.ball z (cutoffDyadicBallRadius R n))
    let shellCoeff (n : ℕ) := cutoffDyadicBallWeight γ α R N n
    have hshellRoot n (hn : n ∈ Finset.range (N + 1)) :
        (∫⁻ ω, (shellCoeff n * shellMass n ω) ^ p ∂P) ^ (1 / p) ≤
          A * ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) *
            halfRatio ^ (n + 1) := by
      have hnle : n ≤ N := by
        have := Finset.mem_range.mp hn
        omega
      have hRn : cutoffDyadicBallRadius R n ≤ R := by
        dsimp [cutoffDyadicBallRadius]
        apply (div_le_iff₀ (by positivity)).2
        exact le_mul_of_one_le_right hR.le (one_le_pow₀ (by norm_num))
      have hmassBase := hballRoot z (cutoffDyadicBallRadius R n) δ
        (by dsimp [cutoffDyadicBallRadius]; positivity) (hRn.trans hRsmall) hδ (hNhi.trans (by dsimp [cutoffDyadicBallRadius]; exact div_le_div_of_nonneg_left hR.le (by positivity) (pow_le_pow_right₀ (by norm_num) hnle))) (by linarith only [hchart, hRn])
      have hρnext : 0 < cutoffDyadicBallRadius R (n + 1) := by
        dsimp [cutoffDyadicBallRadius]
        positivity
      rw [(show shellCoeff n = ENNReal.ofReal (cutoffDyadicBallRadius R (n + 1) ^ (-γ * α)) by simp [shellCoeff, cutoffDyadicBallWeight, hnle])]
      calc
        _ = ENNReal.ofReal
            (cutoffDyadicBallRadius R (n + 1) ^ (-γ * α)) *
              (∫⁻ ω, ENNReal.rpow (shellMass n ω) p ∂P) ^ (1 / p) := (ennreal_lintegral_rpow_const_mul_root_eq p hp0 (ENNReal.ofReal (cutoffDyadicBallRadius R (n + 1) ^ (-γ * α))) ENNReal.ofReal_lt_top (shellMass n) (by exact regularizedGMC_mass_aemeasurable P X hX Xc hXc γ (Real.log (1 / δ)) (Metric.ball z (cutoffDyadicBallRadius R n)) Metric.isOpen_ball.measurableSet) hmassBase.2)
        _ ≤ ENNReal.ofReal
            (cutoffDyadicBallRadius R (n + 1) ^ (-γ * α)) *
              (A * ENNReal.ofReal
                ((cutoffDyadicBallRadius R n / (1 / 8 : ℝ)) ^ (xi / p))) :=
          mul_le_mul_of_nonneg_left hmassBase.1 (by positivity)
        _ = A * (ENNReal.ofReal
              (cutoffDyadicBallRadius R (n + 1) ^ (-γ * α)) *
                ENNReal.ofReal
                  ((cutoffDyadicBallRadius R n / (1 / 8 : ℝ)) ^ (xi / p))) := by ac_rfl
        _ = A * (ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) *
              halfRatio ^ (n + 1)) := by rw [(show ENNReal.ofReal (cutoffDyadicBallRadius R (n + 1) ^ (-γ * α)) * ENNReal.ofReal ((cutoffDyadicBallRadius R n / (1 / 8 : ℝ)) ^ (xi / p)) = ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) * halfRatio ^ (n + 1) by rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hρnext.le _), (weighted_cutoff_shell_rpow_identity γ α p R hγ hp0 hR n)]; exact (show ENNReal.ofReal ((2 / (1 / 8 : ℝ)) ^ (xi / p) * R ^ beta * ((1 / 2 : ℝ) ^ beta) ^ (n + 1)) = ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) * halfRatio ^ (n + 1) by dsimp [shellCoefReal, halfRatio, halfRatioReal, beta, xi]; rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]))]
        _ = _ := by ac_rfl
    have hshellSumActual :
        (∑ n ∈ Finset.range (N + 1),
          (∫⁻ ω, (shellCoeff n * shellMass n ω) ^ p ∂P) ^ (1 / p)) ≤
          A * ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) *
            (halfRatio * (1 - halfRatio)⁻¹) := by
      calc
        _ ≤ ∑ n ∈ Finset.range (N + 1),
            A * ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) *
              halfRatio ^ (n + 1) := by
          apply Finset.sum_le_sum
          intro n hn
          exact hshellRoot n hn
        _ ≤ ∑' n : ℕ,
            A * ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) *
              halfRatio ^ (n + 1) := ENNReal.sum_le_tsum _
        _ = A * ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) *
            (halfRatio * (1 - halfRatio)⁻¹) := by
          calc
            _ = ∑' n : ℕ,
                (A * ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) * halfRatio) *
                  halfRatio ^ n := by
              apply tsum_congr
              intro n
              rw [pow_succ]
              ac_rfl
            _ = (A * ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) * halfRatio) *
                ∑' n : ℕ, halfRatio ^ n := ENNReal.tsum_mul_left
            _ = _ := by rw [ENNReal.tsum_geometric]; ac_rfl
    have hgeomCompare : halfRatio * (1 - halfRatio)⁻¹ ≤
        halfRatio0 * (1 - halfRatio0)⁻¹ := by
      calc
        _ ≤ halfRatio0 * (1 - halfRatio)⁻¹ :=
          mul_le_mul_of_nonneg_right hratio (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left (by apply ENNReal.inv_le_inv'; exact (tsub_le_tsub_left hratio 1)) (by positivity)
    have hrootBound :
        (∫⁻ ω, ENNReal.rpow
          (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P) ^ (1 / p) ≤
          K * ENNReal.ofReal (R ^ beta) := by
      calc
        _ ≤ (∫⁻ ω, (coreCoeff * coreMass ω) ^ p ∂P) ^ (1 / p) +
            ∑ n ∈ Finset.range (N + 1),
              (∫⁻ ω, (shellCoeff n * shellMass n ω) ^ p ∂P) ^ (1 / p) := (cutoffWeightedGmcBallMoment_positive_lp_shell_bound P X hX Xc hXc γ α hγ hα z R δ p N hR hδ hNlo hp)
        _ ≤ A * ENNReal.ofReal coreCoefReal * ENNReal.ofReal (R ^ beta) +
            A * ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) *
              (halfRatio0 * (1 - halfRatio0)⁻¹) :=
          add_le_add hcoreRoot (by exact hshellSumActual.trans (mul_le_mul_of_nonneg_left hgeomCompare (by positivity)))
        _ = K * ENNReal.ofReal (R ^ beta) := by
          dsimp [K, D]
          ring
    have hrightPow : (K * ENNReal.ofReal (R ^ beta)) ^ p =
        K ^ p * ENNReal.ofReal (R ^ weightedCutoffMomentScaleExponent γ α p) := by
      rw [ENNReal.mul_rpow_of_ne_top hK.ne ENNReal.ofReal_ne_top]
      have hscalePow := ENNReal.ofReal_rpow_of_pos
        (p := p) (Real.rpow_pos_of_pos hR beta)
      change ENNReal.rpow (ENNReal.ofReal (R ^ beta)) p = ENNReal.ofReal ((R ^ beta) ^ p) at hscalePow
      change K ^ p * ENNReal.rpow (ENNReal.ofReal (R ^ beta)) p =
        K ^ p * ENNReal.ofReal (R ^ weightedCutoffMomentScaleExponent γ α p)
      rw [hscalePow]
      have hReal : (R ^ beta) ^ p =
          R ^ weightedCutoffMomentScaleExponent γ α p := by
        rw [← Real.rpow_mul hR.le]
        dsimp [beta]
        field_simp [ne_of_gt hp0]
      rw [hReal]
    calc
      _ = ((∫⁻ ω, ENNReal.rpow
          (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P) ^ (1 / p)) ^ p :=
        (show ((∫⁻ ω, ENNReal.rpow (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P) ^ (1 / p)) ^ p = ∫⁻ ω, ENNReal.rpow (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P by rw [← ENNReal.rpow_mul]; rw [show 1 / p * p = 1 by field_simp [ne_of_gt hp0], ENNReal.rpow_one]).symm
      _ ≤ (K * ENNReal.ofReal (R ^ beta)) ^ p :=
      ENNReal.rpow_le_rpow hrootBound hp0.le
      _ = K ^ p * ENNReal.ofReal
          (R ^ weightedCutoffMomentScaleExponent γ α p) := hrightPow
      _ = cutoffWeightedPositiveScaleRootBoundConstant A γ p ε ^ p *
          ENNReal.ofReal (R ^ weightedCutoffMomentScaleExponent γ α p) := by rw [hKeq]


end DOZZ.Proofs
