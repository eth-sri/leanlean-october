/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Annulus.ClippedDyadic
public import DOZZ.GMC.Moments.LimitFatou
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# The first sharp positive-moment induction step

The finite-cutoff root identity is assembled with the inner cutoff disk, the bounded
outer mass, and the geometric dyadic sum. All constants are independent of the root
and cutoff. The input at order `p-1` in this first step is the proved first moment.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- The exact polynomial exponent at the order used inside the rooted mass. -/
noncomputable def gmcRootOrderExponent (γ q : ℝ) : ℝ :=
  2 * q + γ ^ 2 * q / 2 - γ ^ 2 * q ^ 2 / 2

/-- The sharp exponent remaining after the singular covariance insertion. -/
noncomputable def gmcRootAnnularExponent (γ q : ℝ) : ℝ := gmcRootOrderExponent γ q - γ ^ 2 * q

/-- The root annular exponent is strictly positive at the next subcritical order. -/
theorem gmcRootAnnularExponent_pos
    γ q (hγ : 0 < γ) (hq : 0 < q) (hcrit : q + 1 < 4 / γ ^ 2) :
    0 < gmcRootAnnularExponent γ q := by
  have := (lt_div_iff₀ (sq_pos_of_pos hγ)).mp hcrit
  rw [(show gmcRootAnnularExponent γ q = q * (2 - γ ^ 2 * (q + 1) / 2) by unfold gmcRootAnnularExponent gmcRootOrderExponent; ring)]
  exact mul_pos hq (by nlinarith)

/-- One finite reference first-moment constant for the entire dyadic calculation. -/
noncomputable def gmcRootSubunitReference (R : ℝ) : ℝ≥0∞ :=
  1 + gmcReferenceMeasure (Metric.ball (0 : ℂ) R)

/-- Explicit innermost-disk comparison constant after discarding only a bounded positive
power of the cutoff radius. -/
noncomputable def gmcRootInnerConstant (γ q R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ (gmcRootOrderExponent γ q) * R ^ (-gmcRootOrderExponent γ q))

/-- Explicit geometric-series comparison constant for the active dyadic scales. -/
noncomputable def gmcRootDyadicConstant (γ q R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (R ^ (-γ ^ 2 * q) * (2 : ℝ) ^ (γ ^ 2 * q)) *
    (1 - ENNReal.ofReal ((2 : ℝ) ^ (-gmcRootAnnularExponent γ q)))⁻¹

/-- The complete clipped-mass moment constant includes all three source pieces. -/
noncomputable def gmcRootClippedConstant (γ q R : ℝ) : ℝ≥0∞ :=
  (gmcRootInnerConstant γ q R + ENNReal.ofReal (R ^ (-γ ^ 2 * q)) +
    gmcRootDyadicConstant γ q R) * gmcRootSubunitReference R

/-- The reference factor is finite on every spatial radius. -/
theorem gmcRootSubunitReference_lt_top R : gmcRootSubunitReference R < ∞ := by
  let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  exact ENNReal.add_lt_top.mpr ⟨by simp, measure_lt_top _ _⟩







/-- Coarse and fine cutoff estimates together give one uniform reference bound at every
cutoff `t>=0`, for every subcritical order in the first induction interval. -/
theorem regularizedGMC_reference_positive_moment_uniform_upto_two
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    Xc (hXc : IsCircleAverage P X Xc)
    γ p (hγ : 0 < γ) (hp : 1 < p) (hp2 : p ≤ 2) (hcrit : p < 4 / γ ^ 2)
    {R} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ t : ℝ, 0 ≤ t →
      gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball 0 R) p ≤ C := by
  have regularizedGMC_reference_positive_moment_fine_upto_two (hcrit : p < 4 / γ ^ 2) {R} {t} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (ht : 0 ≤ t) (hcut : 2 * Real.exp (-t) ≤ R) : gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball 0 R) p ≤ ENNReal.ofReal (Real.exp (γ ^ 2 * gmcCircleChartRemainder R * (p - 1))) * (gmcRootClippedConstant γ (p - 1) R * gmcReferenceMeasure (Metric.ball 0 R)) := by
    have regularizedGMC_root_clipped_moment_uniform (q : ℝ) (hγ : 0 < γ) (hq : 0 < q) (hq1 : q ≤ 1) (hcrit : q + 1 < 4 / γ ^ 2) {R} {t} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (hcut : 2 * Real.exp (-t) ≤ R) u (hu : ‖u‖ ≤ R) : (∫⁻ ω, (∫⁻ x in Metric.ball (0 : ℂ) R, ENNReal.ofReal ((max ‖x - u‖ (Real.exp (-t))) ^ (-γ ^ 2)) ∂regularizedGMC P Xc γ t ω) ^ q ∂P) ≤ gmcRootClippedConstant γ q R := by
      have regularizedGMC_root_dyadic_moment_uniform {t} : (∫⁻ ω, (∑' n : ℕ, gmcClippedDyadicTerm (regularizedGMC P Xc γ t ω) γ R (Real.exp (-t)) u n) ^ q ∂P) ≤ gmcRootDyadicConstant γ q R * gmcRootSubunitReference R := by
        calc
          _ ≤ ∫⁻ ω, ∑' n : ℕ, (gmcClippedDyadicTerm (regularizedGMC P Xc γ t ω)
              γ R (Real.exp (-t)) u n) ^ q ∂P := by
            apply lintegral_mono
            intro ω
            exact ennreal_rpow_tsum_le_tsum_rpow _ hq hq1
          _ = ∑' n : ℕ, ∫⁻ ω, (gmcClippedDyadicTerm (regularizedGMC P Xc γ t ω)
              γ R (Real.exp (-t)) u n) ^ q ∂P := lintegral_tsum (fun n => ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (measurable_regularizedGMC_clipped_dyadic_term P X hX Xc hXc γ R t u n).aemeasurable)
          _ ≤ _ := regularizedGMC_clipped_dyadic_subunit_moment_sum_bound P X hX Xc hXc γ q hq hq1
            hR hRsmall u hu
      have regularizedGMC_root_inner_moment_uniform (hγ : 0 < γ) (hq : 0 < q) (hq1 : q ≤ 1) (hcrit : q + 1 < 4 / γ ^ 2) {R} {t} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (hcut : 2 * Real.exp (-t) ≤ R) u (hu : ‖u‖ ≤ R) : (∫⁻ ω, (ENNReal.ofReal ((Real.exp (-t)) ^ (-γ ^ 2)) * regularizedGMC P Xc γ t ω (Metric.ball u (2 * Real.exp (-t)))) ^ q ∂P) ≤ gmcRootInnerConstant γ q R * gmcRootSubunitReference R := by
        exact (regularizedGMC_inner_clipped_subunit_moment_bound P X hX Xc hXc γ q hq hq1 hR hRsmall hcut u hu).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left (Real.rpow_le_one (Real.exp_nonneg _) (by linarith) (gmcRootAnnularExponent_pos γ q hγ hq hcrit).le) (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hR.le _))).trans_eq (mul_one _))) le_rfl)
      let I : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal ((Real.exp (-t)) ^ (-γ ^ 2)) *
        regularizedGMC P Xc γ t ω (Metric.ball u (2 * Real.exp (-t)))
      let O : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (R ^ (-γ ^ 2)) *
        regularizedGMC P Xc γ t ω (Metric.ball 0 R)
      let S : Ω → ℝ≥0∞ := fun ω => ∑' n : ℕ,
        gmcClippedDyadicTerm (regularizedGMC P Xc γ t ω) γ R (Real.exp (-t)) u n
      have hI : Measurable (fun ω => (I ω) ^ q) :=
        ENNReal.continuous_rpow_const.measurable.comp (measurable_const.mul
          ((Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp
            (regularizedGMC_measurable P X hX Xc hXc γ t)))
      have hb : (∫⁻ ω, (O ω) ^ q ∂P) ≤
          ENNReal.ofReal (R ^ (-γ ^ 2 * q)) * gmcRootSubunitReference R := by
        simp only [O, ENNReal.mul_rpow_of_nonneg _ _ hq.le,
          ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hR _), ← Real.rpow_mul hR.le]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact mul_le_mul' le_rfl (regularizedGMC_subunit_moment_uniform P X hX Xc hXc γ t q
          hq.le hq1 (Metric.ball 0 R) Metric.isOpen_ball.measurableSet)
      calc
        _ ≤ ∫⁻ ω, (I ω) ^ q + (O ω) ^ q + (S ω) ^ q ∂P := by
          apply lintegral_mono
          intro ω
          exact (ENNReal.rpow_le_rpow (gmc_clipped_mass_le_dyadic (regularizedGMC P Xc γ t ω) γ R (Real.exp (-t)) hR (Real.exp_pos _) u (Metric.ball 0 R)) hq.le).trans ((ENNReal.rpow_add_le_add_rpow (I ω + O ω) (S ω) hq.le hq1).trans
            (add_le_add (ENNReal.rpow_add_le_add_rpow (I ω) (O ω) hq.le hq1) le_rfl))
        _ = (∫⁻ ω, (I ω) ^ q ∂P) + (∫⁻ ω, (O ω) ^ q ∂P) + (∫⁻ ω, (S ω) ^ q ∂P) := by
          have hIO : AEMeasurable (fun ω => (I ω) ^ q + (O ω) ^ q) P := (hI.add (ENNReal.continuous_rpow_const.measurable.comp (measurable_const.mul ((Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp (regularizedGMC_measurable P X hX Xc hXc γ t))))).aemeasurable
          rw [lintegral_add_left' hIO, lintegral_add_left' hI.aemeasurable]
        _ ≤ (gmcRootInnerConstant γ q R * gmcRootSubunitReference R) +
            (ENNReal.ofReal (R ^ (-γ ^ 2 * q)) * gmcRootSubunitReference R) +
              (gmcRootDyadicConstant γ q R * gmcRootSubunitReference R) :=
          add_le_add (add_le_add (regularizedGMC_root_inner_moment_uniform
            hγ hq hq1 hcrit hR hRsmall hcut u hu) hb)
              (regularizedGMC_root_dyadic_moment_uniform)
        _ = _ := by unfold gmcRootClippedConstant; rw [add_mul, add_mul]
    have hchart : ∀ x ∈ Metric.ball (0 : ℂ) R, ‖x‖ ≤ R := by
      intro x hx
      exact (show ‖x‖ < R by simpa only [Metric.mem_ball, dist_zero_right] using hx).le
    have h := regularizedGMC_positive_moment_le_clipped P X hX Xc hXc γ R t p hR.le ht hp
      (Metric.ball 0 R) Metric.isOpen_ball.measurableSet hchart
    change gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball 0 R) p ≤ _ at h
    have hbound : (∫⁻ u in Metric.ball (0 : ℂ) R, ∫⁻ ω,
        (∫⁻ x in Metric.ball (0 : ℂ) R, ENNReal.ofReal
          ((max ‖x - u‖ (Real.exp (-t))) ^ (-γ ^ 2)) ∂regularizedGMC P Xc γ t ω) ^ (p - 1)
            ∂P ∂gmcReferenceMeasure) ≤
          gmcRootClippedConstant γ (p - 1) R * gmcReferenceMeasure (Metric.ball 0 R) := by
      calc
        _ ≤ ∫⁻ _u in Metric.ball (0 : ℂ) R, gmcRootClippedConstant γ (p - 1) R ∂gmcReferenceMeasure := by
          apply setLIntegral_mono' Metric.isOpen_ball.measurableSet
          intro u hu
          exact regularizedGMC_root_clipped_moment_uniform (p - 1) hγ (by linarith) (by linarith) (by simpa only [sub_add_cancel] using hcrit)
            hR hRsmall hcut u (hchart u hu)
        _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]
    exact h.trans (mul_le_mul' le_rfl hbound)
  have gmcRootClippedConstant_lt_top q R (hγ : 0 < γ) (hq : 0 < q) (hcrit : q + 1 < 4 / γ ^ 2) : gmcRootClippedConstant γ q R < ∞ := by
    unfold gmcRootClippedConstant
    exact ENNReal.mul_lt_top (ENNReal.add_lt_top.mpr
      ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩,
        (by exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr (by intro h; exact (not_le_of_gt (gmc_clipped_dyadic_ratio_lt_one γ q hγ hq hcrit)) (tsub_eq_zero_iff_le.mp h)))))⟩) (gmcRootSubunitReference_lt_top R)
  let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  let T := Real.log (2 / R)
  refine ⟨(ENNReal.ofReal (Real.exp (γ ^ 2 * gmcCircleChartRemainder R * (p - 1))) * (gmcRootClippedConstant γ (p - 1) R * gmcReferenceMeasure (Metric.ball 0 R))) + ((gmcReferenceMeasure (Metric.ball (0 : ℂ) R)) ^ p * ENNReal.ofReal (Real.exp (γ ^ 2 * (p ^ 2 - p) / 2 * (T + gmcCircleChartRemainder R)))), ENNReal.add_lt_top.mpr ⟨(ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top (gmcRootClippedConstant_lt_top (p - 1) R hγ (by linarith) (by simpa only [sub_add_cancel] using hcrit)) (measure_lt_top _ _))), (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg (by linarith) (measure_ne_top _ _))) ENNReal.ofReal_lt_top)⟩, ?_⟩
  intro t ht
  by_cases hcut : 2 * Real.exp (-t) ≤ R
  · exact (regularizedGMC_reference_positive_moment_fine_upto_two
      hcrit hR hRsmall ht hcut).trans (le_add_of_nonneg_right zero_le)
  · have htT : t ≤ T := by
      exact (neg_lt_neg_iff.mp (Real.exp_lt_exp.mp (by rw [(show Real.exp (-T) = R / 2 by dsimp [T]; rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) hR), inv_div])]; linarith))).le
    exact (regularizedGMC_coarse_chart_moment_upper P X hX Xc hXc γ R T p hR.le hp.le
      (Metric.ball 0 R) Metric.isOpen_ball.measurableSet (by intro x hx; exact (show ‖x‖ < R by simpa only [Metric.mem_ball, dist_zero_right] using hx).le) t ht htT).trans
        (le_add_of_nonneg_left zero_le)

/-- The continuous ball approximants have integral no larger than the actual open-ball mass. -/
theorem gmc_ball_approx_ofReal_integral_le_mass
    (μ : Measure ℂ) [IsFiniteMeasure μ] z R n :
    ENNReal.ofReal (∫ x, openBallApprox z R n x ∂μ) ≤ μ (Metric.ball z R) := by
  have hnonneg (x : ℂ) := (openBallApproxFun_bounds z R n x).1
  have hpoint x : ENNReal.ofReal (openBallApprox z R n x) ≤
      (Metric.ball z R).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    by_cases hx : x ∈ Metric.ball z R
    · rw [Set.indicator_of_mem hx]
      exact ENNReal.ofReal_le_one.mpr (openBallApproxFun_bounds z R n x).2
    · have hn : R ≤ ‖x - z‖ := le_of_not_gt (by simpa only [Metric.mem_ball, dist_eq_norm] using hx)
      change ENNReal.ofReal (max 0 (min 1 ((n : ℝ) * (R - ‖x - z‖)))) ≤ _
      rw [max_eq_left ((min_le_right _ _).trans (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (sub_nonpos.mpr hn))), ENNReal.ofReal_zero]
      exact zero_le
  rw [ofReal_integral_eq_lintegral_ofReal ((openBallApprox z R n).integrable (μ := μ)) (ae_of_all μ hnonneg)]
  have h := lintegral_mono (μ := μ) hpoint
  rwa [lintegral_indicator_const Metric.isOpen_ball.measurableSet, one_mul] at h

end DOZZ.Proofs
