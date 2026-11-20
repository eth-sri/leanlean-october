/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.GMC.AdmissibleGMCRestriction
public import DOZZ.GMC.Moments.RegularizedScale
public import DOZZ.GMC.Moments.ChaosLawFDDLimit
public import DOZZ.GMC.Moments.ScaleLimit
public import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
public import DOZZ.GMC.Moments.OpenBallApproximation
public import DOZZ.GMC.Moments.ExactScaleBallMoment
public import DOZZ.GMC.Annulus.PositiveRoot
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import DOZZ.GMC.Moments.CutoffBallScale
public import DOZZ.GMC.Moments.PositiveExponent

/-! Exact affine scaling of actual finite-cutoff open-ball masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (γ : ℝ) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) {a : ℂ} {c R r : ℝ} (hc : 0 < c)
  (hc1 : c ≤ 1) (hR : 0 < R) (hRsmall : R < 1) (hTsmall : ‖a‖ + c * R < 1)
  (hsourceCut : ∀ x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R},
      ‖x.1‖ + Real.exp (-r) ≤ 1)
  (htargetCut : ∀ x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R},
      ‖a + c • x.1‖ + Real.exp (-(r - Real.log c)) ≤ 1)
include Ω X hX hXc hc hc1 hR hRsmall hTsmall hsourceCut htargetCut

/-- For actual circle cutoff measures, affine scaling preserves the full ball-mass law,
including the independent scalar Gaussian and the corresponding change of cutoff. -/
theorem regularizedGMC_affine_openBall_mass_law_CutoffScale :
    Measure.map (fun ω : Ω =>
      (regularizedGMC P Xc γ (r - Real.log c) ω (Metric.ball a (c * R))).toReal) P =
    Measure.map (fun p : Ω × ℝ =>
      c ^ 2 * Real.exp (γ * p.2 - γ ^ 2 / 2 * (-Real.log c)) *
        (regularizedGMC P Xc γ r p.1 (Metric.ball 0 R)).toReal)
      (P.prod (gaussianReal 0 ⟨-Real.log c,
        neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩)) :=
  regularizedGMC_affine_openBall_mass_law P X hX Xc hXc γ hc hc1 hR hsourceCut htargetCut
    (norm_le_one_of_mem_closedBall_in_chart (a := 0) (by simpa using hRsmall.le))
    (norm_le_one_of_mem_closedBall_in_chart hTsmall.le)


/-- Exact moment scaling at the actual finite cutoff, for every real order. -/
theorem regularizedGMC_affine_openBall_moment_scale_CutoffScale (p : ℝ) :
    gmcMassMoment P (regularizedGMC P Xc γ (r - Real.log c)) (Metric.ball a (c * R)) p =
    ENNReal.ofReal (c ^ (gmcScaleExponent γ p)) *
      gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball 0 R) p :=
  regularizedGMC_affine_openBall_moment_scale P X hX Xc hXc γ hc hc1 hR hsourceCut htargetCut
    (norm_le_one_of_mem_closedBall_in_chart (a := 0) (by simpa using hRsmall.le))
    (norm_le_one_of_mem_closedBall_in_chart hTsmall.le) p


end


/-- Radius-form finite-cutoff scaling. The reference cutoff is shifted by `log(s/R)`;
its circle radius is consequently the original circle radius multiplied by `R/s`.
The two explicit radius guards ensure all averaging circles stay in the exact chart. -/
theorem regularizedGMC_local_ball_moment_scale
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (z : ℂ) {s R t : ℝ} (hs : 0 < s) (hsR : s ≤ R) (hR : 0 < R)
    (hR1 : R < 1) (hz : ‖z‖ + s < 1)
    (hbase : R + Real.exp (-t) * (R / s) ≤ 1)
    (htarget : ‖z‖ + s + Real.exp (-t) ≤ 1) (p : ℝ) :
    gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball z s) p =
      ENNReal.ofReal ((s / R) ^ (gmcScaleExponent γ p)) *
        gmcMassMoment P (regularizedGMC P Xc γ (t + Real.log (s / R)))
          (Metric.ball 0 R) p := by
  have hc  := div_pos hs hR
  have hc1  := (div_le_one hR).mpr hsR
  have he : Real.exp (-(t + Real.log (s / R))) = Real.exp (-t) * (R / s) := by
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log (s / R)), Real.exp_log hc, inv_div]
  have hsEq  := div_mul_cancel₀ s hR.ne'
  have hsource : ∀ x : {w : ℂ // w ∈ Metric.closedBall (0 : ℂ) R},
      ‖x.1‖ + Real.exp (-(t + Real.log (s / R))) ≤ 1 := by
    intro x
    have hx : ‖x.1‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using x.2
    rw [he]
    exact (add_le_add hx le_rfl).trans hbase
  have htar : ∀ x : {w : ℂ // w ∈ Metric.closedBall (0 : ℂ) R},
      ‖z + (s / R) • x.1‖ + Real.exp (-((t + Real.log (s / R)) - Real.log (s / R))) ≤ 1 := by
    intro x
    have hx : ‖x.1‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using x.2
    have hn : ‖z + (s / R) • x.1‖ ≤ ‖z‖ + s := by
      calc
        _ ≤ ‖z‖ + ‖(s / R) • x.1‖ := norm_add_le _ _
        _ = ‖z‖ + (s / R) * ‖x.1‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
        _ ≤ ‖z‖ + (s / R) * R := add_le_add le_rfl (mul_le_mul_of_nonneg_left hx hc.le)
        _ = _ := by rw [hsEq]
    rw [add_sub_cancel_right]
    exact (add_le_add hn le_rfl).trans htarget
  have h := regularizedGMC_affine_openBall_moment_scale_CutoffScale P X hX γ Xc hXc
    (a := z) (c := s / R) (R := R) (r := t + Real.log (s / R)) hc hc1 hR hR1
    (by simpa only [hsEq] using hz) hsource htar p
  simpa only [add_sub_cancel_right, hsEq] using h

/-- Spatial Hölder in the extended positive reals, including zero and infinite integrals. -/
theorem ennreal_lintegral_rpow_le_mass_rpow_mul_lintegral_rpow
    {S : Type*} [MeasurableSpace S] (ν : Measure S) (f : S → ℝ≥0∞)
    (hf : AEMeasurable f ν) (p : ℝ) (hp : 1 ≤ p) :
    (∫⁻ x, f x ∂ν) ^ p ≤ (ν univ) ^ (p - 1) * ∫⁻ x, (f x) ^ p ∂ν := by
  rcases hp.eq_or_lt with hp | hp
  · subst p
    simp
  · let q := p / (p - 1)
    have hc : p.HolderConjugate q := by
      apply Real.holderConjugate_iff.mpr
      grind
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hc hf
      (aemeasurable_const : AEMeasurable (fun _ : S => (1 : ℝ≥0∞)) ν)
    simp only [Pi.mul_apply, ENNReal.one_rpow, mul_one, lintegral_one] at h
    have he : (1 / q) * p = p - 1 := by
      dsimp [q]
      field_simp [ne_of_gt (by linarith : 0 < p), ne_of_gt (by linarith : 0 < p - 1)]
    have hp0 : 0 ≤ p := by linarith
    have hpne : p ≠ 0 := by linarith
    have hpow := ENNReal.rpow_le_rpow h hp0
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      one_div_mul_cancel hpne, ENNReal.rpow_one, he, mul_comm] at hpow
    exact hpow

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
include Ω X hX hXc

theorem regularizedGMC_moment_upper_of_variance_bound
    (γ r p V : ℝ) (hp : 1 ≤ p)
    (O : Set ℂ) (hO : MeasurableSet O)
    (hvar : ∀ x ∈ O, gaussianVariance P (fun ω => Xc ω x r) ≤ V) :
    gmcMassMoment P (regularizedGMC P Xc γ r) O p ≤
      (gmcReferenceMeasure O) ^ p * ENNReal.ofReal
        (Real.exp (γ ^ 2 * (p ^ 2 - p) / 2 * V)) := by
  let _ := hX.1
  let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  have hW := measurable_gmcCircleWickDensity P X Xc hXc γ r
  have hWp : Measurable (fun q : Ω × ℂ => (gmcCircleWickDensity P Xc γ r q.1 q.2) ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp hW
  have hf (ω : Ω) : AEMeasurable (gmcCircleWickDensity P Xc γ r ω)
      (gmcReferenceMeasure.restrict O) :=
    (hW.comp (measurable_const.prodMk measurable_id)).aemeasurable
  change (∫⁻ ω, (regularizedGMC P Xc γ r ω O) ^ p ∂P) ≤ _
  calc
    _ ≤ ∫⁻ ω, (gmcReferenceMeasure O) ^ (p - 1) *
        ∫⁻ x in O, (gmcCircleWickDensity P Xc γ r ω x) ^ p ∂gmcReferenceMeasure ∂P := by
      apply lintegral_mono
      intro ω
      change (regularizedGMC P Xc γ r ω O) ^ p ≤ (gmcReferenceMeasure O) ^ (p - 1) *
        ∫⁻ x in O, (gmcCircleWickDensity P Xc γ r ω x) ^ p ∂gmcReferenceMeasure
      rw [regularizedGMC_mass_eq_wick_lintegral P X Xc hXc γ r O hO ω]
      have h := ennreal_lintegral_rpow_le_mass_rpow_mul_lintegral_rpow
        (gmcReferenceMeasure.restrict O) (gmcCircleWickDensity P Xc γ r ω) (hf ω) p hp
      simpa only [Measure.restrict_apply_univ] using h
    _ = (gmcReferenceMeasure O) ^ (p - 1) *
        ∫⁻ x in O, ∫⁻ ω, (gmcCircleWickDensity P Xc γ r ω x) ^ p ∂P ∂gmcReferenceMeasure := by
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
        (measure_ne_top _ _)), lintegral_lintegral_swap hWp.aemeasurable]
    _ ≤ (gmcReferenceMeasure O) ^ (p - 1) * (gmcReferenceMeasure O *
        ENNReal.ofReal (Real.exp (γ ^ 2 * (p ^ 2 - p) / 2 * V))) := by
      apply mul_le_mul' le_rfl
      calc
        _ ≤ ∫⁻ _x in O, ENNReal.ofReal (Real.exp
            (γ ^ 2 * (p ^ 2 - p) / 2 * V)) ∂gmcReferenceMeasure := by
          apply setLIntegral_mono' hO
          intro x hx
          rw [gmcCircleWickDensity_moment P X hX Xc hXc γ r p x]
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_left (hvar x hx)
          exact div_nonneg (mul_nonneg (sq_nonneg γ) (by nlinarith)) (by norm_num)
        _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]
    _ = _ := by
      have he : (gmcReferenceMeasure O) ^ (p - 1) * gmcReferenceMeasure O =
          (gmcReferenceMeasure O) ^ p := by
        calc
          _ = (gmcReferenceMeasure O) ^ (p - 1) * (gmcReferenceMeasure O) ^ (1 : ℝ) :=
            by rw [ENNReal.rpow_one]
          _ = (gmcReferenceMeasure O) ^ ((p - 1) + 1) :=
            (ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by norm_num)).symm
          _ = _ := by congr 1; ring
      rw [← mul_assoc, he]

/-- The actual mass at a coarse cutoff has a uniform higher-moment estimate on every bounded
Borel chart. The reference measure and covariance remainder both appear explicitly. -/
theorem regularizedGMC_coarse_chart_moment_upper
    (γ R T p : ℝ) (hR : 0 ≤ R) (hp : 1 ≤ p)
    (O : Set ℂ) (hO : MeasurableSet O) (hchart : ∀ x ∈ O, ‖x‖ ≤ R)
    (r : ℝ) (hr : 0 ≤ r) (hrT : r ≤ T) :
    gmcMassMoment P (regularizedGMC P Xc γ r) O p ≤
      (gmcReferenceMeasure O) ^ p * ENNReal.ofReal
        (Real.exp (γ ^ 2 * (p ^ 2 - p) / 2 * (T + gmcCircleChartRemainder R))) :=
  regularizedGMC_moment_upper_of_variance_bound P X hX Xc hXc γ r p _ hp O hO
    (fun x hx => gmcCircle_variance_le_coarse_chart P X hX Xc hXc R r T hR hr hrT x (hchart x hx))

end


end DOZZ.Proofs
