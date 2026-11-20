/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.RegularizedScale
public import DOZZ.GMC.Moments.OpenBallApproximation
public import DOZZ.GMC.Moments.CutoffSubunit
public import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
public import DOZZ.GMC.Moments.ChaosLawFDDLimit
public import DOZZ.GMC.Moments.ScaleLimit
public import DOZZ.GMC.Moments.ExactScaleBallMoment
public import DOZZ.GMC.Moments.PositiveExponent

/-! Exact affine scaling for open-ball masses of the finite circle-cutoff chaos. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ) {a : ℂ} {c R r : ℝ} (hc : 0 < c)
  (hc1 : c ≤ 1) (hR : 0 < R)
  (hsourceCut : ∀ x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R},
      ‖x.1‖ + Real.exp (-r) ≤ 1)
  (htargetCut : ∀ x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R},
      ‖a + c • x.1‖ + Real.exp (-(r - Real.log c)) ≤ 1)
  (hsourceUnit : ∀ x ∈ Metric.closedBall (0 : ℂ) R, ‖x‖ ≤ 1)
  (htargetUnit : ∀ x ∈ Metric.closedBall a (c * R), ‖x‖ ≤ 1)
include Ω X hX hXc hc hc1 hR hsourceCut htargetCut hsourceUnit htargetUnit

/-- The finite-cutoff affine test-vector law passes to open-ball masses. The cutoff radius is
scaled together with the disk, and the common Gaussian shift contributes the same scalar as in
the test-vector identity. -/
theorem regularizedGMC_affine_openBall_mass_law :
    Measure.map (fun ω : Ω =>
      (regularizedGMC P Xc γ (r - Real.log c) ω (Metric.ball a (c * R))).toReal) P =
    Measure.map (fun q : Ω × ℝ =>
      c ^ 2 * Real.exp (γ * q.2 - γ ^ 2 / 2 * (-Real.log c)) *
        (regularizedGMC P Xc γ r q.1 (Metric.ball 0 R)).toReal)
      (P.prod (gaussianReal 0 ⟨-Real.log c,
        neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩)) := by
  have := hX.1
  let G := gaussianReal 0 ⟨-Real.log c, neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩
  have : IsProbabilityMeasure G := ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _
  refine affine_openBall_mass_law_of_tests P G _ _
    (regularizedGMC_finite_ae P X hX Xc hXc γ (r - Real.log c))
    (regularizedGMC_finite_ae P X hX Xc hXc γ r) hc
    (fun w => c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * (-Real.log c))) (by fun_prop) ?_ ?_ ?_
  · intro n
    exact regularizedGMC_test_integral_aemeasurable P X hX Xc hXc γ _
      (openBallAffineApprox a c R n) (openBallAffineApprox a c R n).continuous.measurable
  · intro n
    exact regularizedGMC_test_integral_aemeasurable P X hX Xc hXc γ _
      (openBallApprox 0 R n) (openBallApprox 0 R n).continuous.measurable
  · intro n
    exact regularizedGMC_affine_cutoff_test_vector_law P X hX Xc hXc γ hc hc1 hR hsourceCut htargetCut
      (fun _ => openBallAffineApprox a c R n)
      (fun _ x => (openBallApproxFun_bounds 0 R n ((c : ℂ)⁻¹ • (x - a))).1)
      (fun _ => openBallAffineApprox_tsupport_subset hc n)

/-- Every real moment of a finite-cutoff open-ball mass obeys the exact affine scaling law. -/
theorem regularizedGMC_affine_openBall_moment_scale
    (p : ℝ) :
    ∫⁻ ω, ENNReal.rpow
      (regularizedGMC P Xc γ (r - Real.log c) ω (Metric.ball a (c * R))) p ∂P =
      ENNReal.ofReal (c ^ (gmcScaleExponent γ p)) *
        ∫⁻ ω, ENNReal.rpow (regularizedGMC P Xc γ r ω (Metric.ball 0 R)) p ∂P := by
  have := hX.1
  refine gaussianScaleFactor_massMoment_of_law P γ c p hc hc1 _ _
    (regularizedGMC_mass_aemeasurable P X hX Xc hXc γ _ _ Metric.isOpen_ball.measurableSet)
    (regularizedGMC_mass_aemeasurable P X hX Xc hXc γ _ _ Metric.isOpen_ball.measurableSet) ?_ ?_ ?_
  · filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ (r - Real.log c)] with ω hw
    exact measure_ne_top _ _
  · filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ r] with ω hw
    exact measure_ne_top _ _
  · exact regularizedGMC_affine_openBall_mass_law P X hX Xc hXc γ hc hc1 hR hsourceCut htargetCut
      hsourceUnit htargetUnit

end

/-- A finite-cutoff ball mass at scales no finer than its cutoff has the exact subunit scaling
bound obtained from the reference half-disk intensity. -/
theorem regularizedGMC_openBall_subunit_scale_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ : ℝ) (z : ℂ) (s δ p : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1 / 2) (hδ : 0 < δ) (hδs : δ ≤ s)
    (hchart : ‖z‖ + 2 * s ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫⁻ ω, ENNReal.rpow
      (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z s)) p ∂P ≤
      ENNReal.ofReal ((2 * s) ^
        (gmcScaleExponent γ p)) *
        (1 + gmcReferenceMeasure (Metric.ball 0 (1 / 2))) := by
  let c  := 2 * s
  let r  := Real.log (1 / δ) + Real.log c
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by dsimp [c]; linarith
  have hδc : Real.exp (-r) = δ / c := by
    have hδrec : Real.exp (-Real.log (1 / δ)) = δ := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    have hcrec : Real.exp (-Real.log c) = c⁻¹ := by
      rw [Real.exp_neg, Real.exp_log hc]
    rw [show -r = -Real.log (1 / δ) + -Real.log c by dsimp [r]; ring,
      Real.exp_add, hδrec, hcrec]
    dsimp [c]
    field_simp
  have htargetCutoff : Real.exp (-(r - Real.log c)) = δ := by
    have hr : r - Real.log c = Real.log (1 / δ) := by
      dsimp [r]
      ring
    rw [hr]
    have hδrec : Real.exp (-Real.log (1 / δ)) = δ := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    exact hδrec
  have hsourceCut : ∀ x : {w : ℂ // w ∈ Metric.closedBall (0 : ℂ) (1 / 2 : ℝ)},
      ‖x.1‖ + Real.exp (-r) ≤ 1 := by
    intro x
    have hx : ‖x.1‖ ≤ (1 / 2 : ℝ) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using x.2
    have hδcHalf : δ / c ≤ (1 / 2 : ℝ) := by
      dsimp [c]
      exact (div_le_iff₀ (by positivity)).2 (by nlinarith [hδs])
    rw [hδc]
    linarith
  have htargetCut : ∀ x : {w : ℂ // w ∈ Metric.closedBall (0 : ℂ) (1 / 2 : ℝ)},
      ‖z + c • x.1‖ + Real.exp (-(r - Real.log c)) ≤ 1 := by
    intro x
    have hx : ‖x.1‖ ≤ (1 / 2 : ℝ) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using x.2
    have hnorm : ‖z + c • x.1‖ ≤ ‖z‖ + s := by
      calc
        ‖z + c • x.1‖ ≤ ‖z‖ + ‖c • x.1‖ := norm_add_le _ _
        _ = ‖z‖ + c * ‖x.1‖ := by simp [abs_of_pos hc]
        _ ≤ ‖z‖ + c * (1 / 2 : ℝ) := by
          nlinarith [mul_le_mul_of_nonneg_left hx hc.le]
        _ = ‖z‖ + s := by dsimp [c]; ring
    rw [htargetCutoff]
    nlinarith [hchart]
  have hsourceUnit : ∀ x ∈ Metric.closedBall (0 : ℂ) (1 / 2 : ℝ), ‖x‖ ≤ 1 := by
    intro x hx
    have hx' : ‖x‖ ≤ (1 / 2 : ℝ) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    linarith
  have hrad : c * (1 / 2 : ℝ) = s := by dsimp [c]; ring
  have htargetUnit : ∀ x ∈ Metric.closedBall z (c * (1 / 2 : ℝ)), ‖x‖ ≤ 1 := by
    intro x hx
    have hx'' : ‖x - z‖ ≤ s := by
      have hx' : ‖x - z‖ ≤ c * (1 / 2 : ℝ) := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx
      rw [hrad] at hx'
      exact hx'
    have hnorm : ‖x‖ ≤ ‖z‖ + s := by
      calc
        ‖x‖ = ‖(x - z) + z‖ := by congr 1; ring
        _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ s + ‖z‖ := add_le_add hx'' le_rfl
        _ = ‖z‖ + s := by ring
    exact le_trans hnorm (by nlinarith [hchart])
  have hscale := regularizedGMC_affine_openBall_moment_scale P X hX Xc hXc γ
    (a := z) (c := c) (R := (1 / 2 : ℝ)) (r := r) hc hc1
    (by norm_num) hsourceCut htargetCut hsourceUnit htargetUnit p
  have htargetParam : r - Real.log c = Real.log (1 / δ) := by
    dsimp [r]
    ring
  rw [htargetParam, hrad] at hscale
  have hbase := regularizedGMC_subunit_moment_le P X hX Xc hXc γ r
    (Metric.ball 0 (1 / 2)) Metric.isOpen_ball.measurableSet p hp hp1
  calc
    _ = ENNReal.ofReal (c ^
          (gmcScaleExponent γ p)) *
        ∫⁻ ω, ENNReal.rpow
          (regularizedGMC P Xc γ r ω (Metric.ball 0 (1 / 2))) p ∂P := hscale
    _ ≤ ENNReal.ofReal (c ^
          (gmcScaleExponent γ p)) *
        (1 + gmcReferenceMeasure (Metric.ball 0 (1 / 2))) :=
      by gcongr
    _ = _ := by rfl

end DOZZ.Proofs
