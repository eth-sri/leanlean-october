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

/-! Local test-integral representations needed to transfer exact scaling from circle fields to the
regularized GMC measures `DOZZ.regularizedGMC`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]

section
variable (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ)
  (hXc : IsCircleAverage P X Xc) (γ r : ℝ) (K : Set ℂ) (hK : MeasurableSet K)
  (hK_unit : ∀ x ∈ K, ‖x‖ ≤ 1) (f : ℂ → ℝ) (hf : Measurable f) (hf_zero : ∀ x, x ∉ K → f x = 0)
include hX hXc γ r hK hK_unit hf hf_zero

private lemma regularizedGMC_test_integral_eq_local_wick (ω : Ω) :
    (∫ x, f x ∂regularizedGMC P Xc γ r ω) =
      ∫ x in K, f x * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 *
        gaussianVariance P (fun ω' => Xc ω' x r)) ∂volume := by
  have _ := hf
  let := hX.1
  let V : ℂ → ℝ := fun x => ∫ ω', Xc ω' x r ^ 2 ∂P
  have hVarEq (x : ℂ) : gaussianVariance P (fun ω' => Xc ω' x r) = V x := by
    simp [V, gaussianVariance, gaussianCovariance, pow_two]
  have hVm : Measurable V := by
    convert circleAverage_variance_measurable (P := P) Xc hXc.1 r using 1
    exact funext fun x => (hVarEq x).symm
  have hnpm : Measurable normPlus := measurable_const.max measurable_norm
  have hXcω : Measurable fun x : ℂ => Xc ω x r := (hXc.1 r).comp (measurable_const.prodMk measurable_id)
  have hDω : Measurable fun x : ℂ => ENNReal.ofReal
      (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x) * normPlus x ^ (-4 : ℝ)) := by fun_prop
  rw [regularizedGMC, integral_withDensity_eq_integral_toReal_smul hDω (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    integral_restrict_eq_integral_of_zero_on_compl volume K hK
      (fun x => f x * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * gaussianVariance P (fun ω' => Xc ω' x r)))
      (fun x hx => by simp [hf_zero x hx])]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  have hnppos : 0 < normPlus x := zero_lt_one.trans_le (le_max_left 1 ‖x‖)
  rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul, hVarEq]
  by_cases hx : x ∈ K
  · have hnp1 : normPlus x = 1 := max_eq_left (hK_unit x hx)
    rw [hnp1]; simp [mul_comm]
  · simp [hf_zero x hx]

/-- Compactly supported cutoff tests are measurable random variables. -/
theorem regularizedGMC_test_integral_aemeasurable :
    AEMeasurable (fun ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) P := by
  classical
  let := hX.1
  let H : Ω × ℂ → ℝ := fun p => if p.2 ∈ K then f p.2 * Real.exp
    (γ * Xc p.1 p.2 r - γ ^ 2 / 2 * gaussianVariance P (fun ω => Xc ω p.2 r)) else 0
  have hH : Measurable H := Measurable.ite (hK.preimage measurable_snd)
    ((hf.comp measurable_snd).mul (Real.measurable_exp.comp
      ((measurable_const.mul (hXc.1 r)).sub (measurable_const.mul
        ((circleAverage_variance_measurable (P := P) Xc hXc.1 r).comp measurable_snd)))))
    measurable_const
  have hI : Measurable fun ω => ∫ x, H (ω, x) ∂volume :=
    hH.stronglyMeasurable.integral_prod_right'.measurable
  exact hI.aemeasurable.congr (ae_of_all _ fun ω => by
    dsimp only
    rw [regularizedGMC_test_integral_eq_local_wick P X hX Xc hXc γ r K hK hK_unit f hf hf_zero ω,
      ← integral_indicator hK]
    rfl)

end

/-- The regularized measures `DOZZ.regularizedGMC` obey exact affine scaling on compactly supported
chart tests at matching cutoffs. -/
theorem regularizedGMC_affine_cutoff_test_vector_law {m : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ : ℝ) {a : ℂ} {c R r : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hR : 0 < R)
    (hsourceCut : ∀ x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R},
      ‖x.1‖ + Real.exp (-r) ≤ 1)
    (htargetCut : ∀ x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R},
      ‖a + c • x.1‖ + Real.exp (-(r - Real.log c)) ≤ 1)
    (hsourceUnit : ∀ x ∈ Metric.closedBall (0 : ℂ) R, ‖x‖ ≤ 1)
    (htargetUnit : ∀ x ∈ Metric.closedBall a (c * R), ‖x‖ ≤ 1)
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
  let : MeasureSpace S := Measure.Subtype.measureSpace
  let ν := localBallProbability R
  let : IsProbabilityMeasure ν := localBallProbability_isProbability hR
  let := hX.1
  let G := gaussianReal 0 ⟨-Real.log c, neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩
  let : IsProbabilityMeasure G := ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _
  let area := (ENNReal.ofReal R ^ 2 * (NNReal.pi : ℝ≥0∞)).toReal
  have harea (g : ℂ → ℝ) : (∫ x in Metric.closedBall (0 : ℂ) R, g x ∂volume) =
      area * ∫ x : S, g x.1 ∂ν := by
    let vol := (volume : Measure S) Set.univ
    have hvol : vol = ENNReal.ofReal R ^ 2 * (NNReal.pi : ℝ≥0∞) := by
      dsimp [vol, S]
      rw [Measure.Subtype.volume_univ Metric.isClosed_closedBall.measurableSet.nullMeasurableSet,
        Complex.volume_closedBall]
    have h0 : vol ≠ 0 := by
      rw [hvol]
      exact (ENNReal.mul_pos (pow_ne_zero 2 (ENNReal.ofReal_ne_zero_iff.mpr hR))
        (ENNReal.coe_ne_zero.mpr NNReal.pi_pos.ne')).ne'
    have htop : vol ≠ ⊤ := by rw [hvol]; exact ENNReal.mul_ne_top (by simp) (by simp)
    rw [← integral_subtype Metric.isClosed_closedBall.measurableSet g,
      show ν = vol⁻¹ • (volume : Measure S) from rfl, integral_smul_measure, smul_eq_mul,
      ← mul_assoc, show area * (vol⁻¹).toReal = 1 by
        dsimp [area]; rw [← hvol, ← ENNReal.toReal_mul, ENNReal.mul_inv_cancel h0 htop]; simp,
      one_mul]
  let weight : Fin m → S → ℝ := fun j x => f j (a + c • x.1)
  have hwm : ∀ j, Measurable (weight j) := by fun_prop
  have hwint (j : Fin m) : Integrable (weight j) ν :=
    (integrable_const ‖f j‖).mono' (hwm j).aestronglyMeasurable
      (ae_of_all _ fun x => (f j).norm_coe_le_norm _)
  let vBase : S → ℝ≥0 := fun x => (gaussianVariance P (fun ω => Xc ω x.1 r)).toNNReal
  let vTot : S → ℝ≥0 := fun x => (gaussianVariance P (fun ω => Xc ω (a + c • x.1) (r - Real.log c))).toNNReal
  have hvBm : Measurable vBase := (measurable_real_toNNReal.comp
    (circleAverage_variance_measurable (P := P) Xc hXc.1 r)).comp measurable_subtype_coe
  have hvTm : Measurable vTot := (measurable_real_toNNReal.comp
    (circleAverage_variance_measurable (P := P) Xc hXc.1 (r - Real.log c))).comp
    (by fun_prop : Measurable fun x : S => a + c • x.1)
  let tWick : Ω → Fin m → ℝ := fun ω j => ∫ x, weight j x * Real.exp
    (γ * Xc ω (a + c • x.1) (r - Real.log c) - γ ^ 2 / 2 * (vTot x : ℝ)) ∂ν
  let bWick : Ω → Fin m → ℝ := fun ω j => ∫ x, weight j x * Real.exp
    (γ * Xc ω x.1 r - γ ^ 2 / 2 * (vBase x : ℝ)) ∂ν
  have htWm : Measurable tWick := measurable_pi_iff.2 fun j =>
    (((hwm j).comp measurable_snd).mul (Real.measurable_exp.comp
      ((measurable_const.mul ((hXc.1 (r - Real.log c)).comp
        (by dsimp [S]; fun_prop : Measurable fun p : Ω × S => (p.1, a + c • p.2.1)))).sub
        (measurable_const.mul (measurable_coe_nnreal_real.comp (hvTm.comp measurable_snd)))))).stronglyMeasurable.integral_prod_right'.measurable
  have hbWm : Measurable bWick := measurable_pi_iff.2 fun j =>
    (((hwm j).comp measurable_snd).mul (Real.measurable_exp.comp
      ((measurable_const.mul ((hXc.1 r).comp
        (by dsimp [S]; fun_prop : Measurable fun p : Ω × S => (p.1, p.2.1)))).sub
        (measurable_const.mul (measurable_coe_nnreal_real.comp (hvBm.comp measurable_snd)))))).stronglyMeasurable.integral_prod_right'.measurable
  let fac : Ω × ℝ → ℝ := fun p => Real.exp (γ * p.2 - γ ^ 2 / 2 * (-Real.log c))
  have hwickLaw : Measure.map tWick P =
      Measure.map (fun p : Ω × ℝ => fun j => fac p * bWick p.1 j) (P.prod G) :=
    circleAverage_affine_scaled_wick_integral_law X Xc hX hXc ν
      (a := a) (c := c) (r := r) (γ := γ) hc hc1 Subtype.val measurable_subtype_coe
      hsourceCut htargetCut weight hwm (fun j x => hf_nonneg j _) hwint
  let A : (Fin m → ℝ) → Fin m → ℝ := fun v j => (c ^ 2 * area) * v j
  have hAm : Measurable A := by fun_prop
  have himg := complex_affine_image_closedBall (a := a) (R := R) hc
  have hf0T (j : Fin m) := boundedContinuousFunction_eq_zero_off_tsupport_subset (f j) _ (hf_support j)
  have htEq : (fun ω j => ∫ x, f j x ∂regularizedGMC P Xc γ (r - Real.log c) ω) = A ∘ tWick := by
    ext ω j
    rw [regularizedGMC_test_integral_eq_local_wick P X hX Xc hXc γ (r - Real.log c) _
      Metric.isClosed_closedBall.measurableSet htargetUnit (f j) (f j).continuous.measurable (hf0T j) ω]
    let g : ℂ → ℝ := fun y => f j y * Real.exp
      (γ * Xc ω y (r - Real.log c) - γ ^ 2 / 2 * gaussianVariance P (fun ω' => Xc ω' y (r - Real.log c)))
    have hg : Measurable g := (f j).continuous.measurable.mul (Real.measurable_exp.comp
      ((measurable_const.mul ((hXc.1 _).comp (measurable_const.prodMk measurable_id))).sub
        (measurable_const.mul (circleAverage_variance_measurable (P := P) Xc hXc.1 _))))
    have hch := complex_integral_affine_restrict (a := a) hc.ne' (Metric.closedBall (0 : ℂ) R)
      (by rw [himg]; exact Metric.isClosed_closedBall.measurableSet) g hg
    rw [← himg]
    have hjac : (|(c ^ 2)⁻¹|)⁻¹ = c ^ 2 := by
      rw [abs_of_pos (inv_pos.mpr (sq_pos_of_ne_zero hc.ne')), inv_inv]
    have h1 : (∫ y in (fun x => a + c • x) '' Metric.closedBall 0 R, g y) =
        c ^ 2 * ∫ x in Metric.closedBall 0 R, g (a + c • x) := by simpa [hjac] using hch
    rw [h1, harea]
    dsimp only [Function.comp_apply, A, tWick, weight, g]
    rw [mul_assoc]; congr 2; refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only [vTot]
    rw [Real.coe_toNNReal _ (circleAverage_gaussian_law_and_variance_nonneg P X hX Xc hXc _ _).2]
  have hbEq : (fun p : Ω × ℝ => fun j => c ^ 2 * fac p *
      ∫ x, f j (a + c • x) ∂regularizedGMC P Xc γ r p.1) =
      A ∘ fun p : Ω × ℝ => fun j => fac p * bWick p.1 j := by
    ext p j
    have hf0B (x : ℂ) (hx : x ∉ Metric.closedBall (0 : ℂ) R) : f j (a + c • x) = 0 :=
      hf0T j _ fun hy => by
        rw [← himg] at hy; rcases hy with ⟨y, hyB, hyEq⟩
        exact hx (smul_right_injective ℂ hc.ne' (add_left_cancel hyEq.symm) ▸ hyB)
    rw [regularizedGMC_test_integral_eq_local_wick P X hX Xc hXc γ r _
      Metric.isClosed_closedBall.measurableSet hsourceUnit (fun x => f j (a + c • x))
      (by fun_prop) hf0B p.1, harea]
    dsimp only [Function.comp_apply, A, bWick, weight, vBase]
    have : ∫ x : S, f j (a + c • x.1) * Real.exp (γ * Xc p.1 x.1 r -
        γ ^ 2 / 2 * gaussianVariance P (fun ω' => Xc ω' x.1 r)) ∂ν =
      ∫ x : S, f j (a + c • x.1) * Real.exp (γ * Xc p.1 x.1 r -
        γ ^ 2 / 2 * ((gaussianVariance P (fun ω => Xc ω x.1 r)).toNNReal : ℝ)) ∂ν :=
      integral_congr_ae (ae_of_all _ fun x => by
        dsimp only
        rw [Real.coe_toNNReal _ (circleAverage_gaussian_law_and_variance_nonneg P X hX Xc hXc _ _).2])
    rw [this]; ring
  rw [htEq, ← Measure.map_map hAm htWm, hwickLaw,
    Measure.map_map hAm (by dsimp [fac]; fun_prop), ← hbEq]

end DOZZ.Proofs
