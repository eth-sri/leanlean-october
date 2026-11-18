/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Annulus.PositiveBase
public import DOZZ.GMC.Annulus.BallCover
public import DOZZ.Brownian.Lateral.UpperConditionedBlocks

/-!
# Higher-order clipped-scale moment estimates
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]


section
variable (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ p : ℝ) (hγ : 0 < γ)
include hX hXc p hγ

private lemma ref_moment_step
 (hp : 2 ≤ p) (hcrit : p < 4 / γ ^ 2)
    {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (C : ℝ≥0∞) (hC : C < ∞)
    (hRef : ∀ r : ℝ, 0 ≤ r → gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball 0 R) (p - 1) ≤ C) :
    ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ t : ℝ, 0 ≤ t →
      gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball 0 R) p ≤ B := by
  have local_ball_upper_of_ref (q : ℝ) {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (C : ℝ≥0∞) (hRef : ∀ r : ℝ, 0 ≤ r → gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball 0 R) q ≤ C) {s t : ℝ} (hs : 0 < s) (hsR : s ≤ R) (hcut : Real.exp (-t) ≤ s) (z : ℂ) (hz : ‖z‖ ≤ R) : gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball z s) q ≤
        ENNReal.ofReal ((s / R) ^ gmcRootOrderExponent γ q) * C := by
    have hsc : Real.exp (-(t + Real.log (s / R))) = Real.exp (-t) * (R / s) := by
      rw [neg_add, Real.exp_add, Real.exp_neg (Real.log (s / R)), Real.exp_log (div_pos hs hR), inv_div]
    have hleR : Real.exp (-t) * (R / s) ≤ R :=
      (mul_le_mul_of_nonneg_right hcut (div_nonneg hR.le hs.le)).trans_eq (by field_simp)
    have hr : 0 ≤ t + Real.log (s / R) :=
      neg_nonpos.1 (Real.exp_le_one_iff.1 (by rw [hsc]; linarith))
    rw [regularizedGMC_local_ball_moment_scale P X hX γ Xc hXc z hs hsR hR (by linarith)
      (by linarith) (by linarith) (by linarith) q]
    exact mul_le_mul' le_rfl (hRef _ hr)
  let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  let q := p - 1
  have hq : 1 ≤ q := by dsimp [q]; linarith
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hcritq : q + 1 < 4 / γ ^ 2 := by dsimp [q]; linarith
  let a := ENNReal.ofReal ((2 : ℝ) ^ (-gmcRootAnnularExponent γ q))
  let D := ENNReal.ofReal (R ^ (-γ ^ 2 * q) * (2 : ℝ) ^ (γ ^ 2 * q))
  let Kdyad := (D ^ (1 / q) * (1 - a ^ (1 / q))⁻¹ * C ^ (1 / q)) ^ q
  let Kclip := (3 : ℝ≥0∞) ^ q * (gmcRootInnerConstant γ q R * C +
    ENNReal.ofReal (R ^ (-γ ^ 2 * q)) * C + Kdyad)
  have hd0 : 1 - a ^ (1 / q) ≠ 0 := fun h =>
    (not_le_of_gt (ENNReal.rpow_lt_one (gmc_clipped_dyadic_ratio_lt_one γ q hγ hq0 hcritq)
      (one_div_pos.2 hq0))) (tsub_eq_zero_iff_le.1 h)
  have hKdyad : Kdyad < ∞ := lt_top_iff_ne_top.2 (ENNReal.rpow_ne_top_of_nonneg hq0.le
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (one_div_pos.2 hq0).le ENNReal.ofReal_ne_top)
      (ENNReal.inv_ne_top.2 hd0)) (ENNReal.rpow_ne_top_of_nonneg (one_div_pos.2 hq0).le hC.ne)))
  have hKclip : Kclip < ∞ := ENNReal.mul_lt_top
    (lt_top_iff_ne_top.2 (ENNReal.rpow_ne_top_of_nonneg hq0.le (by simp)))
    (ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC⟩, hKdyad⟩)
  let T := Real.log (2 / R)
  let F := ENNReal.ofReal (Real.exp (γ ^ 2 * gmcCircleChartRemainder R * q)) *
    (Kclip * gmcReferenceMeasure (Metric.ball 0 R))
  let B0 := gmcReferenceMeasure (Metric.ball (0 : ℂ) R) ^ p *
    ENNReal.ofReal (Real.exp (γ ^ 2 * (p ^ 2 - p) / 2 * (T + gmcCircleChartRemainder R)))
  have hF : F < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top hKclip (measure_lt_top _ _))
  have hB0 : B0 < ∞ := ENNReal.mul_lt_top
    (lt_top_iff_ne_top.2 (ENNReal.rpow_ne_top_of_nonneg (by linarith) (measure_ne_top _ _)))
    ENNReal.ofReal_lt_top
  have hchart : ∀ x ∈ Metric.ball (0 : ℂ) R, ‖x‖ ≤ R :=
    fun x hx => (by simpa [Metric.mem_ball, dist_zero_right] using hx : ‖x‖ < R).le
  refine ⟨F + B0, ENNReal.add_lt_top.2 ⟨hF, hB0⟩, fun t ht => ?_⟩
  by_cases hcut : 2 * Real.exp (-t) ≤ R
  · have hclip_u (u : ℂ) (hu : ‖u‖ ≤ R) :
        (∫⁻ ω, (∫⁻ x in Metric.ball (0 : ℂ) R,
          ENNReal.ofReal (max ‖x - u‖ (Real.exp (-t)) ^ (-γ ^ 2))
          ∂regularizedGMC P Xc γ t ω) ^ q ∂P) ≤ Kclip := by
      let δ := Real.exp (-t)
      have hδ : 0 < δ := Real.exp_pos _
      let I (ω : Ω) := ENNReal.ofReal (δ ^ (-γ ^ 2)) * regularizedGMC P Xc γ t ω (Metric.ball u (2 * δ))
      let O (ω : Ω) := ENNReal.ofReal (R ^ (-γ ^ 2)) * regularizedGMC P Xc γ t ω (Metric.ball 0 R)
      let S (ω : Ω) := ∑' n : ℕ, gmcClippedDyadicTerm (regularizedGMC P Xc γ t ω) γ R δ u n
      have hIm : Measurable fun ω => I ω ^ q := ENNReal.continuous_rpow_const.measurable.comp
        (measurable_const.mul ((Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp
          (regularizedGMC_measurable P X hX Xc hXc γ t)))
      have hOm : Measurable fun ω => O ω ^ q := ENNReal.continuous_rpow_const.measurable.comp
        (measurable_const.mul ((Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp
          (regularizedGMC_measurable P X hX Xc hXc γ t)))
      have h3 (a₁ b₁ c₁ : ℝ≥0∞) : (a₁ + b₁ + c₁) ^ q ≤ (3 : ℝ≥0∞) ^ q * (a₁ ^ q + b₁ ^ q + c₁ ^ q) := by
        simpa [Fin.sum_univ_succ, add_assoc] using ennreal_finset_sum_rpow_le_card_rpow_sum
          (Finset.univ : Finset (Fin 3)) ⟨0, Finset.mem_univ 0⟩ ![a₁, b₁, c₁] q hq0.le
      have hbI : (∫⁻ ω, I ω ^ q ∂P) ≤ gmcRootInnerConstant γ q R * C := by
        let ξ := gmcRootOrderExponent γ q
        simp only [I, ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
          ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hδ (-γ ^ 2)), ← Real.rpow_mul hδ.le]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        have hb := mul_le_mul' (le_refl (ENNReal.ofReal (δ ^ (-γ ^ 2 * q))))
          (local_ball_upper_of_ref q hR hRsmall C hRef
            (mul_pos zero_lt_two hδ) hcut (by linarith) u hu)
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _),
          show δ ^ (-γ ^ 2 * q) * (2 * δ / R) ^ ξ = (2 : ℝ) ^ ξ * R ^ (-ξ) * δ ^ (ξ - γ ^ 2 * q) by
            rw [Real.div_rpow (by positivity) hR.le, Real.mul_rpow zero_le_two hδ.le,
              div_eq_mul_inv, ← Real.rpow_neg hR.le, sub_eq_add_neg, Real.rpow_add hδ]; ring] at hb
        exact hb.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
          ((mul_le_mul_of_nonneg_left (Real.rpow_le_one hδ.le (by linarith)
            (gmcRootAnnularExponent_pos γ q hγ hq0 hcritq).le)
            (mul_nonneg (Real.rpow_nonneg zero_le_two _) (Real.rpow_nonneg hR.le _))).trans_eq (mul_one _))) le_rfl)
      have hbO : (∫⁻ ω, O ω ^ q ∂P) ≤ ENNReal.ofReal (R ^ (-γ ^ 2 * q)) * C := by
        simp only [O, ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
          ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hR (-γ ^ 2)), ← Real.rpow_mul hR.le]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact mul_le_mul' le_rfl (hRef t ht)
      have hbS : (∫⁻ ω, S ω ^ q ∂P) ≤ Kdyad := by
        let Fn (n : ℕ) (ω : Ω) := gmcClippedDyadicTerm (regularizedGMC P Xc γ t ω) γ R δ u n
        have hbn (n : ℕ) : (∫⁻ ω, Fn n ω ^ q ∂P) ^ (1 / q) ≤ D ^ (1 / q) * (a ^ (1 / q)) ^ n * C ^ (1 / q) := by
          have hterm : (∫⁻ ω, Fn n ω ^ q ∂P) ≤ D * a ^ n * C := by
            by_cases ha_n : δ ≤ gmcDyadicRadius R n
            · have hn : 0 < gmcDyadicRadius R n := by unfold gmcDyadicRadius; positivity
              have hnR : gmcDyadicRadius R n ≤ R := by
                unfold gmcDyadicRadius; rw [div_le_iff₀ (by positivity)]
                exact (mul_one R).symm.trans_le (mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num)) hR.le)
              have hn1 : 0 < gmcDyadicRadius R (n + 1) := by unfold gmcDyadicRadius; positivity
              simp only [Fn, gmcClippedDyadicTerm, ha_n, ↓reduceIte, ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
                ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hn1 (-γ ^ 2)), ← Real.rpow_mul hn1.le]
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
              have h := mul_le_mul' (le_refl (ENNReal.ofReal (gmcDyadicRadius R (n + 1) ^ (-γ ^ 2 * q))))
                (local_ball_upper_of_ref q hR hRsmall C hRef hn hnR ha_n u hu)
              rwa [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hn1.le _),
                gmc_dyadic_weight_scale_eq_geometric γ q (gmcRootOrderExponent γ q) R hR n,
                ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)] at h
            · simp [Fn, gmcClippedDyadicTerm, ha_n, ENNReal.zero_rpow_of_pos hq0]
          refine (ENNReal.rpow_le_rpow hterm (one_div_pos.2 hq0).le).trans_eq ?_
          rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.2 hq0).le,
            ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.2 hq0).le,
            ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
          congr 2; congr 1; ring
        have hs := ENNReal.tsum_le_tsum hbn
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric] at hs
        exact (lintegral_tsum_rpow_le_root_moments_power P Fn
          (fun n => (measurable_regularizedGMC_clipped_dyadic_term P X hX Xc hXc γ R t u n).aemeasurable)
          q hq).trans (ENNReal.rpow_le_rpow hs hq0.le)
      calc _ ≤ ∫⁻ ω, (3 : ℝ≥0∞) ^ q * (I ω ^ q + O ω ^ q + S ω ^ q) ∂P :=
            lintegral_mono fun ω => (ENNReal.rpow_le_rpow (gmc_clipped_mass_le_dyadic
              (regularizedGMC P Xc γ t ω) γ R δ hR hδ u (Metric.ball 0 R)) hq0.le).trans (h3 _ _ _)
        _ = (3 : ℝ≥0∞) ^ q * ((∫⁻ ω, I ω ^ q ∂P) + (∫⁻ ω, O ω ^ q ∂P) + ∫⁻ ω, S ω ^ q ∂P) := by
            have hIO : AEMeasurable (fun ω => I ω ^ q + O ω ^ q) P := (hIm.add hOm).aemeasurable
            rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0.le (by simp)),
              lintegral_add_left' hIO, lintegral_add_left' hIm.aemeasurable]
        _ ≤ Kclip := mul_le_mul' le_rfl (add_le_add (add_le_add hbI hbO) hbS)
    have h := regularizedGMC_positive_moment_le_clipped P X hX Xc hXc γ R t p hR.le ht
      (by linarith) (Metric.ball 0 R) Metric.isOpen_ball.measurableSet hchart
    have hb : (∫⁻ u in Metric.ball (0 : ℂ) R, ∫⁻ ω,
        (∫⁻ x in Metric.ball (0 : ℂ) R, ENNReal.ofReal (max ‖x - u‖ (Real.exp (-t)) ^ (-γ ^ 2))
          ∂regularizedGMC P Xc γ t ω) ^ q ∂P ∂gmcReferenceMeasure) ≤
        Kclip * gmcReferenceMeasure (Metric.ball 0 R) := by
      refine (setLIntegral_mono' Metric.isOpen_ball.measurableSet fun u hu => hclip_u u (hchart u hu)).trans_eq ?_
      rw [lintegral_const, Measure.restrict_apply_univ]
    exact (h.trans (mul_le_mul' le_rfl hb)).trans le_self_add
  · have htT : t ≤ T := by
      have he : Real.exp (-T) = R / 2 := by
        dsimp [T]; rw [Real.exp_neg, Real.exp_log (div_pos zero_lt_two hR), inv_div]
      exact (neg_lt_neg_iff.1 (Real.exp_lt_exp.1 (by rw [he]; linarith))).le
    exact (regularizedGMC_coarse_chart_moment_upper P X hX Xc hXc γ R T p hR.le (by linarith)
      (Metric.ball 0 R) Metric.isOpen_ball.measurableSet hchart t ht htT).trans le_add_self

/-- Integer-interval induction closes every strictly subcritical positive reference moment
above one, uniformly in the actual circle cutoff. -/
theorem regularizedGMC_reference_positive_moment_uniform
 (hp : 1 < p) (hcrit : p < 4 / γ ^ 2)
    {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ t : ℝ, 0 ≤ t →
      gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball 0 R) p ≤ C := by
  have hstep : ∀ n : ℕ, ∀ p : ℝ, 1 < p → p ≤ (n : ℝ) + 2 → p < 4 / γ ^ 2 →
      ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ t : ℝ, 0 ≤ t →
        gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball 0 R) p ≤ C := fun n => by
    induction n with
    | zero =>
      exact fun p hp hp2 hcrit => regularizedGMC_reference_positive_moment_uniform_upto_two P X hX Xc hXc γ p hγ hp
        (by simpa using hp2) hcrit hR hRsmall
    | succ n ih =>
      intro p hp hpn hcrit
      by_cases hsmall : p ≤ (n : ℝ) + 2
      · exact ih p hp hsmall hcrit
      · obtain ⟨C, hC, hRef⟩ := ih (p - 1) (by linarith [Nat.cast_nonneg (α := ℝ) n])
          (by push_cast at hpn; linarith) (by linarith)
        exact ref_moment_step P X hX Xc hXc γ p hγ (by linarith [Nat.cast_nonneg (α := ℝ) n]) hcrit hR hRsmall C hC hRef
  obtain ⟨n, hn⟩ := exists_nat_gt p
  exact hstep n p hp (by linarith [Nat.cast_nonneg (α := ℝ) n]) hcrit

/-- The starting subunit range and higher-order induction together cover every positive
order in the literal sharp range, uniformly over all nonnegative cutoff parameters. -/
theorem regularizedGMC_reference_moment_uniform_nonnegative
 (hp : 0 ≤ p) (hcrit : p < 4 / γ ^ 2)
    {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ t : ℝ, 0 ≤ t →
      gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball 0 R) p ≤ C := by
  by_cases hp1 : p ≤ 1
  · exact ⟨gmcRootSubunitReference R, gmcRootSubunitReference_lt_top R, fun t _ =>
      regularizedGMC_subunit_moment_uniform P X hX Xc hXc γ t p hp hp1 _ Metric.isOpen_ball.measurableSet⟩
  · exact regularizedGMC_reference_positive_moment_uniform P X hX Xc hXc γ p hγ (lt_of_not_ge hp1) hcrit hR hRsmall


end
/-- All nonnegative limiting reference moments in the sharp range are finite, including the
subunit starting range and zero order. -/
theorem gmc_reference_nonnegative_moment_finite
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ p : ℝ) (hγ : 0 < γ) (hp : 0 ≤ p) (hcrit : p < 4 / γ ^ 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) :
    gmcMassMoment P M (Metric.ball 0 R) p < ∞ := by
  by_cases hp1 : p ≤ 1
  · let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
    exact (gmc_mass_subunit_moment_bound P X hX γ M hM (Metric.ball 0 R) hp hp1).trans_lt
      (ENNReal.add_lt_top.2 ⟨by simp, measure_lt_top _ _⟩)
  · let _ := hX.1
    have hp' := lt_of_not_ge hp1
    obtain ⟨Xc, hXc, hlimit⟩ := hM.2
    obtain ⟨C, hC, hbound⟩ := regularizedGMC_reference_positive_moment_uniform P X hX Xc hXc γ p hγ hp' hcrit hR hRsmall
    let f (k : ℕ) := openBallApprox 0 R k
    let F (k : ℕ) (ω : Ω) := ∫ x, f k x ∂M ω
    have hcut (k n : ℕ) : AEMeasurable (fun ω => ∫ x, f k x ∂regularizedGMC P Xc γ n ω) P :=
      regularizedGMC_test_integral_aemeasurable P X hX Xc hXc γ n (Metric.closedBall 0 R)
        Metric.isClosed_closedBall.measurableSet
        (fun x hx => (by simpa [Metric.mem_closedBall, dist_zero_right] using hx : ‖x‖ ≤ R).trans (by linarith))
        (f k) (f k).continuous.measurable
        (boundedContinuousFunction_eq_zero_off_tsupport_subset (f k) _ (openBallApprox_tsupport_subset 0 R k))
    have hconv (k : ℕ) := (hlimit (f k)).comp tendsto_natCast_atTop_atTop
    have hF (k : ℕ) := (hconv k).aemeasurable (hcut k)
    have hFn (k : ℕ) (ω : Ω) : 0 ≤ F k ω := integral_nonneg fun x => (openBallApproxFun_bounds 0 R k x).1
    have hfirst (k : ℕ) : (∫⁻ ω, ENNReal.ofReal (F k ω) ^ p ∂P) ≤ C :=
      lintegral_ennreal_rpow_le_of_tendstoInMeasure P _ (F k) p C (hconv k)
        (fun n => ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
          (ENNReal.measurable_ofReal.comp_aemeasurable ((hcut k n).max aemeasurable_const)))
        (ae_of_all P (hFn k)) fun n =>
          (lintegral_mono_ae ((regularizedGMC_finite_ae P X hX Xc hXc γ n).mono fun ω hfin => by
            let _ := hfin
            dsimp only [Function.comp_apply]
            rw [max_eq_left (integral_nonneg fun x => (openBallApproxFun_bounds 0 R k x).1)]
            exact ENNReal.rpow_le_rpow
              (gmc_ball_approx_ofReal_integral_le_mass (regularizedGMC P Xc γ n ω) 0 R k) hp)).trans
            (hbound n (Nat.cast_nonneg n))
    let G (ω : Ω) := (M ω (Metric.ball 0 R)).toReal
    have hseq : TendstoInMeasure P F atTop G :=
      tendstoInMeasure_of_tendsto_ae (fun k => (hF k).aestronglyMeasurable) (ae_of_all _ fun ω => by
        let _ := hM.1 ω; simpa [F, f, G, measureReal_def] using openBallApprox_integral_tendsto 0 R (M ω))
    have hf := lintegral_ennreal_rpow_le_of_tendstoInMeasure P F G p C hseq
      (fun k => ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
        (ENNReal.measurable_ofReal.comp_aemeasurable ((hF k).max aemeasurable_const)))
      (ae_of_all P fun _ => ENNReal.toReal_nonneg) fun k => by
        simpa [max_eq_left (hFn k _)] using hfirst k
    have he : (∫⁻ ω, ENNReal.ofReal (G ω) ^ p ∂P) = gmcMassMoment P M (Metric.ball 0 R) p :=
      lintegral_congr fun ω => by
        let _ := hM.1 ω
        change ENNReal.ofReal (M ω (Metric.ball 0 R)).toReal ^ p = ENNReal.rpow (M ω (Metric.ball 0 R)) p
        rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]; rfl
    change (∫⁻ ω, ENNReal.ofReal (G ω) ^ p ∂P) ≤ C at hf
    exact (he ▸ hf).trans_lt hC

end DOZZ.Proofs
