/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.RegularizedGMC
public import DOZZ.GMC.Moments.LocalBallProbability
public import DOZZ.GMC.Moments.CircleScaleWick
public import DOZZ.GMC.Moments.AffineVolume
public import DOZZ.GMC.AdmissibleGMCRestriction
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure

/-! Local test-integral representations needed to transfer exact scaling from circle fields to the
regularized GMC measures `DOZZ.regularizedGMC`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ) (K : Set ℂ) (hK : MeasurableSet K)
  (hK_unit : ∀ x ∈ K, ‖x‖ ≤ 1) (f : ℂ → ℝ) (hf : Measurable f) (hf_zero : ∀ x, x ∉ K → f x = 0)
include Ω X hX hXc K hK hK_unit hf_zero

/-- On a chart contained in the unit disk, compactly supported cutoff GMC test integrals are
exactly the corresponding Wick integrals against planar volume. -/
theorem regularizedGMC_test_integral_eq_local_wick (ω : Ω) :
    (∫ x, f x ∂regularizedGMC P Xc γ r ω) =
      ∫ x in K, f x * circleWick P Xc γ r ω x ∂volume := by
  let := hX.1
  have hwm : Measurable (circleWick P Xc γ r ω) :=
    (measurable_circleWick (P := P) hXc.1 γ r).comp
    (measurable_const.prodMk (measurable_id : Measurable (id : ℂ → ℂ)))
  have hn : Measurable (fun x : ℂ => normPlus x ^ (-4 : ℝ)) :=
    (measurable_const.max measurable_norm).pow_const _
  rw [regularizedGMC, integral_withDensity_eq_integral_toReal_smul
    (by simpa only [Function.comp_def, Pi.mul_apply, circleWick, gaussianVariance,
      gaussianCovariance, pow_two] using
      ENNReal.measurable_ofReal.comp (hwm.mul hn))
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_restrict_eq_integral_of_zero_on_compl volume K hK _ (fun x hx => by simp [hf_zero x hx])]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_nonneg _)
    (Real.rpow_nonneg (normPlus_pos x).le _))]
  simp only [smul_eq_mul, circleWick, gaussianVariance, gaussianCovariance, pow_two]
  by_cases hx : x ∈ K
  · simp [normPlus, max_eq_left (hK_unit x hx), mul_comm]
  · simp [hf_zero x hx]

end

/-- Test integrals against cutoff chaos are measurable, without a restriction on their support. -/
theorem regularizedGMC_test_integral_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ)
    (f : ℂ → ℝ) (hf : Measurable f) : AEMeasurable (fun ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) P :=
  (measurable_integral_of_measurable_measure (regularizedGMC_measurable P X hX Xc hXc γ r)
    hf.stronglyMeasurable).aemeasurable

/-- A disk-normalized spatial average multiplied by the disk area is the unnormalized planar
integral. -/
theorem localBallProbability_integral_mul_area
    {R : ℝ} (hR : 0 < R)
    (f : ℂ → ℝ) :
    (∫ x in Metric.closedBall (0 : ℂ) R, f x ∂volume) =
      (ENNReal.ofReal R ^ 2 * (NNReal.pi : ℝ≥0∞)).toReal *
        ∫ x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R}, f x.1
          ∂localBallProbability R := by
  let S := {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R}
  let : MeasureSpace S := Measure.Subtype.measureSpace
  rw [← integral_subtype Metric.isClosed_closedBall.measurableSet f,
    localBallProbability, integral_smul_measure, smul_eq_mul, localBallVolume_univ, ← mul_assoc,
    ← ENNReal.toReal_mul, ENNReal.mul_inv_cancel
      (mul_ne_zero (pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.mpr hR))
        (ENNReal.coe_ne_zero.mpr NNReal.pi_pos.ne')) (by finiteness)]
  simp

/-- The regularized measures `DOZZ.regularizedGMC` obey exact affine scaling on compactly supported
chart tests at matching cutoffs. The scalar is independent and has the Gaussian law dictated by the
kernel constant. -/
theorem regularizedGMC_affine_cutoff_test_vector_law
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ : ℝ) {a : ℂ} {c R r : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hR : 0 < R)
    (hsourceCut : ∀ x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R},
      ‖x.1‖ + Real.exp (-r) ≤ 1)
    (htargetCut : ∀ x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R},
      ‖a + c • x.1‖ + Real.exp (-(r - Real.log c)) ≤ 1)
    (f : Fin m → BoundedContinuousFunction ℂ ℝ)
    (hf_nonneg : ∀ j x, 0 ≤ f j x)
    (hf_support : ∀ j, tsupport (f j : ℂ → ℝ) ⊆ Metric.closedBall a (c * R)) :
    Measure.map (fun ω j => ∫ x, f j x ∂regularizedGMC P Xc γ (r - Real.log c) ω) P =
      Measure.map (fun p : Ω × ℝ => fun j => c ^ 2 *
        Real.exp (γ * p.2 - γ ^ 2 / 2 * (-Real.log c)) *
          ∫ x, f j (a + c • x) ∂regularizedGMC P Xc γ r p.1)
        (P.prod (gaussianReal 0 ⟨-Real.log c,
          neg_nonneg.mpr (Real.log_nonpos (le_of_lt hc) hc1)⟩)) := by
  classical
  let S := {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R}
  let ν : Measure S := localBallProbability R
  let : IsProbabilityMeasure ν := localBallProbability_isProbability hR
  let : IsProbabilityMeasure P := hX.1
  let g : ℂ → ℂ := fun x => a + c • x
  have hg : Measurable g := by fun_prop
  have hgi : Function.Injective g := fun _ _ h => (smul_right_injective ℂ hc.ne') (add_left_cancel h)
  have himage : g '' Metric.closedBall 0 R = Metric.closedBall a (c * R) := complex_affine_image_closedBall hc
  have hzero j := boundedContinuousFunction_eq_zero_off_tsupport_subset (f j) _ (hf_support j)
  have hzero' j x (hx : x ∉ Metric.closedBall (0 : ℂ) R) : f j (g x) = 0 :=
    hzero j _ fun h => hx (hgi.mem_set_image.mp (himage ▸ h))
  have hunit x (hx : x ∈ Metric.closedBall (0 : ℂ) R) : ‖x‖ ≤ 1 := by
    linarith [hsourceCut ⟨x, hx⟩, Real.exp_pos (-r)]
  have hunit' x (hx : x ∈ Metric.closedBall a (c * R)) : ‖x‖ ≤ 1 := by
    obtain ⟨y, hy, rfl⟩ := himage ▸ hx
    linarith [htargetCut ⟨y, hy⟩, Real.exp_pos (-(r - Real.log c))]
  let w : Fin m → S → ℝ := fun j x => f j (g x)
  have hw j : Measurable (w j) := (f j).continuous.measurable.comp (hg.comp measurable_subtype_coe)
  have hwi j : Integrable (w j) ν :=
    (integrable_const ‖f j‖).mono' (hw j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => (f j).norm_coe_le_norm (g x))
  have hG (x : ℂ) : a + (c : ℂ) * x = g x := by simp [g, Complex.real_smul]
  have hlaw := circleAverage_affine_scaled_wick_integral_law X Xc hX hXc ν hc hc1
    (γ := γ) Subtype.val measurable_subtype_coe hsourceCut
    (fun x => by simpa only [← Complex.real_smul] using htargetCut x)
    w hw (fun j x => hf_nonneg j (g x)) hwi
  let A := (ENNReal.ofReal R ^ 2 * (NNReal.pi : ℝ≥0∞)).toReal
  let T : (Fin m → ℝ) → Fin m → ℝ := fun v j => c ^ 2 * A * v j
  have hmT : Measurable T := by dsimp [T]; fun_prop
  have hbase (ω : Ω) (j : Fin m) :
      (∫ x, f j (g x) ∂regularizedGMC P Xc γ r ω) =
        A * ∫ x : S, w j x * circleWick P Xc γ r ω x ∂ν := by
    rw [regularizedGMC_test_integral_eq_local_wick P X hX Xc hXc γ r _
      Metric.isClosed_closedBall.measurableSet hunit _ (hzero' j), localBallProbability_integral_mul_area hR]
  have htarget (ω : Ω) (j : Fin m) :
      (∫ x, f j x ∂regularizedGMC P Xc γ (r - Real.log c) ω) =
        c ^ 2 * A * (∫ x : S, w j x * circleWick P Xc γ (r - Real.log c) ω (g x) ∂ν) := by
    let b := fun x => f j x * circleWick P Xc γ (r - Real.log c) ω x
    have hbm : Measurable b := (f j).continuous.measurable.mul
      ((measurable_circleWick hXc.1 γ (r - Real.log c)).comp (measurable_const.prodMk measurable_id))
    rw [regularizedGMC_test_integral_eq_local_wick P X hX Xc hXc γ _ _
      Metric.isClosed_closedBall.measurableSet hunit' _ (hzero j)]
    change (∫ x in Metric.closedBall a (c * R), b x ∂volume) = _
    have h := complex_integral_affine_restrict (a := a) hc.ne' (Metric.closedBall 0 R)
      (by rw [← show g = (fun x => a + c • x) from rfl, himage]; exact Metric.isClosed_closedBall.measurableSet) b hbm
    change (∫ x in g '' Metric.closedBall 0 R, b x ∂volume) = _ at h
    rw [himage, localBallProbability_integral_mul_area hR] at h
    simpa only [abs_inv, abs_pow, abs_of_pos hc, inv_inv, ← mul_assoc] using h
  convert (hlaw.comp hmT).map_eq using 2
  · funext ω j
    simpa only [Function.comp_apply, T, hG] using htarget ω j
  · funext p j
    rw [show (∫ x, f j (a + c • x) ∂regularizedGMC P Xc γ r p.1) = _ from hbase p.1 j]
    dsimp [T, Function.comp_def]
    ring

end DOZZ.Proofs
