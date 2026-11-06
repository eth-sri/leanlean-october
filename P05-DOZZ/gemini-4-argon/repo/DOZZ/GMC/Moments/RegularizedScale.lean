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

/-- On a chart contained in the unit disk, compactly supported cutoff GMC test integrals are
exactly the corresponding Wick integrals against planar volume. -/
theorem regularizedGMC_test_integral_eq_local_wick
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    Xc (hXc : IsCircleAverage P X Xc)
    γ r K (hK : MeasurableSet K)
    (hK_unit : ∀ x ∈ K, ‖x‖ ≤ 1) f (hf : Measurable f)
    (hf_zero : ∀ x, x ∉ K → f x = 0) ω :
    (∫ x, f x ∂regularizedGMC P Xc γ r ω) =
      ∫ x in K, f x * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 *
        gaussianVariance P (fun ω' => Xc ω' x r)) ∂volume := by
  have _ := hf
  let : IsProbabilityMeasure P := hX.1
  let V : ℂ → ℝ := fun x => ∫ ω', Xc ω' x r ^ 2 ∂P
  let D : Ω × ℂ → ℝ≥0∞ := fun p => ENNReal.ofReal
    (Real.exp (γ * Xc p.1 p.2 r - γ ^ 2 / 2 * V p.2) * normPlus p.2 ^ (-4 : ℝ))
  have hVarEq x : gaussianVariance P (fun ω' => Xc ω' x r) = V x := by
    simp [V, gaussianVariance, gaussianCovariance, pow_two]
  have : Measurable V := by
    convert (circleAverage_variance_measurable (P := P) Xc hXc.1 r) using 1
    funext x
    exact (hVarEq x).symm
  have := hXc.1 r
  have : Measurable (fun x => normPlus x) := by
    unfold normPlus
    exact measurable_const.max measurable_norm
  have hDω : Measurable (fun x => D (ω, x)) := (show Measurable D by dsimp [D]; fun_prop).comp
    (measurable_const.prodMk measurable_id)
  have hraw : (∫ x, f x ∂regularizedGMC P Xc γ r ω) =
      ∫ x, (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x) *
        normPlus x ^ (-4 : ℝ)) * f x ∂volume := by
    rw [regularizedGMC, integral_withDensity_eq_integral_toReal_smul hDω (show ∀ᵐ x ∂volume, D (ω, x) < ∞ by filter_upwards [] with x; exact ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [] with x
    change (ENNReal.ofReal (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x) *
      normPlus x ^ (-4 : ℝ))).toReal • f x = _
    have : 0 < normPlus x := by
      unfold normPlus
      exact lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖x‖)
    rw [ENNReal.toReal_ofReal (show 0 ≤ Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x) * normPlus x ^ (-4 : ℝ) by positivity), smul_eq_mul]
  have hfactor : ∀ x, (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x) *
      normPlus x ^ (-4 : ℝ)) * f x =
        f x * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x) := by
    intro x
    by_cases hx : x ∈ K
    · have hnp : normPlus x = 1 := by
        unfold normPlus
        rw [max_eq_left (hK_unit x hx)]
      rw [hnp]
      simp
      ring
    · rw [hf_zero x hx]
      simp
  have hVarPoint x : f x * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x) =
      f x * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 *
        gaussianVariance P (fun ω' => Xc ω' x r)) := by
    rw [← hVarEq x]
  rw [hraw]
  calc
    (∫ x, (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x) *
        normPlus x ^ (-4 : ℝ)) * f x ∂volume) =
      ∫ x, f x * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x) ∂volume := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hfactor
    _ = ∫ x, f x * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 *
        gaussianVariance P (fun ω' => Xc ω' x r)) ∂volume := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hVarPoint
    _ = ∫ x in K, f x * Real.exp
        (γ * Xc ω x r - γ ^ 2 / 2 *
          gaussianVariance P (fun ω' => Xc ω' x r)) ∂volume :=
      (integral_restrict_eq_integral_of_zero_on_compl volume K hK _ (by
        intro x hx
        simp [hf_zero x hx])).symm

/-- Compactly supported cutoff tests are measurable random variables. This is needed to pass the
finite-cutoff scaling law to limits specified by `IsGMCOf`. -/
theorem regularizedGMC_test_integral_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ r : ℝ) (K : Set ℂ) (hK : MeasurableSet K)
    (hK_unit : ∀ x ∈ K, ‖x‖ ≤ 1) (f : ℂ → ℝ) (hf : Measurable f)
    (hf_zero : ∀ x, x ∉ K → f x = 0) :
    AEMeasurable (fun ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) P := by
  classical
  let : IsProbabilityMeasure P := hX.1
  let H : Ω × ℂ → ℝ := fun p => f p.2 * Real.exp
    (γ * Xc p.1 p.2 r - γ ^ 2 / 2 * gaussianVariance P (fun ω => Xc ω p.2 r))
  let G : Ω × ℂ → ℝ := fun p => if p.2 ∈ K then H p else 0
  have hGsection (ω : Ω) : (fun x => G (ω, x)) =
      K.indicator (fun x => H (ω, x)) := by
    funext x
    by_cases hx : x ∈ K <;> simp [G, hx]
  have hEq (ω : Ω) :
      (∫ x, f x ∂regularizedGMC P Xc γ r ω) = ∫ x, G (ω, x) ∂volume := by
    calc
      (∫ x, f x ∂regularizedGMC P Xc γ r ω) =
          ∫ x in K, f x * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 *
            gaussianVariance P (fun ω' => Xc ω' x r)) ∂volume :=
        regularizedGMC_test_integral_eq_local_wick P X hX Xc hXc γ r K hK
          hK_unit f hf hf_zero ω
      _ = ∫ x, G (ω, x) ∂volume := by
        rw [hGsection ω]
        dsimp [H]
        exact (integral_indicator hK).symm
  rw [(show (fun ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) = (fun ω => ∫ x, G (ω, x) ∂volume) by funext ω; exact hEq ω)]
  exact ((Measurable.ite (hK.preimage measurable_snd) (by dsimp [H]; exact (hf.comp measurable_snd).mul <| Real.measurable_exp.comp ((measurable_const.mul (hXc.1 r)).sub (measurable_const.mul ((circleAverage_variance_measurable (P := P) Xc hXc.1 r).comp measurable_snd)))) measurable_const).stronglyMeasurable.integral_prod_right'.measurable).aemeasurable


/-- The regularized measures `DOZZ.regularizedGMC` obey exact affine scaling on compactly supported
chart tests at matching cutoffs. The scalar is independent and has the Gaussian law dictated by the
kernel constant. -/
theorem regularizedGMC_affine_cutoff_test_vector_law
    {Ω : Type*} [MeasurableSpace Ω] {m}
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    Xc (hXc : IsCircleAverage P X Xc)
    γ {a} {c R r} (hc : 0 < c) (hc1 : c ≤ 1) (hR : 0 < R)
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
  have localBallProbability_integral_mul_area (f : ℂ → ℝ) : (∫ x in Metric.closedBall (0 : ℂ) R, f x ∂volume) = (ENNReal.ofReal R ^ 2 * (NNReal.pi : ℝ≥0∞)).toReal * ∫ x : {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R}, f x.1 ∂localBallProbability R := by
    let S := {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R}
    let : MeasureSpace S := Measure.Subtype.measureSpace
    let m : ℝ≥0∞ := (volume : Measure S) Set.univ
    have hm : m = ENNReal.ofReal R ^ 2 * (NNReal.pi : ℝ≥0∞) := by
      dsimp [m, S]
      rw [Measure.Subtype.volume_univ
        Metric.isClosed_closedBall.measurableSet.nullMeasurableSet, Complex.volume_closedBall]
    calc
      (∫ x in Metric.closedBall (0 : ℂ) R, f x ∂volume) =
          ∫ x : S, f x.1 ∂(volume : Measure S) := (integral_subtype Metric.isClosed_closedBall.measurableSet f).symm
      _ = m.toReal * ((m⁻¹).toReal * ∫ x : S, f x.1 ∂(volume : Measure S)) := by
            calc
              _ = 1 * ∫ x : S, f x.1 ∂(volume : Measure S) := by simp
              _ = (m.toReal * (m⁻¹).toReal) * ∫ x : S, f x.1 ∂(volume : Measure S) := by
                    rw [(show m.toReal * (m⁻¹).toReal = 1 by rw [← ENNReal.toReal_mul, ENNReal.mul_inv_cancel (show m ≠ 0 by rw [hm]; exact ne_of_gt (ENNReal.mul_pos (pow_ne_zero 2 (ENNReal.ofReal_ne_zero_iff.mpr hR)) (by rw [ENNReal.coe_ne_zero]; exact ne_of_gt NNReal.pi_pos))) (show m ≠ ∞ by rw [hm]; exact ENNReal.mul_ne_top (by simp) (by simp))]; simp)]
              _ = m.toReal * ((m⁻¹).toReal * ∫ x : S, f x.1 ∂(volume : Measure S)) := by ring
      _ = m.toReal * ∫ x : S, f x.1 ∂localBallProbability R := by
            rw [(show (∫ x : S, f x.1 ∂localBallProbability R) = (m⁻¹).toReal * ∫ x : S, f x.1 ∂(volume : Measure S) by rw [localBallProbability, integral_smul_measure, smul_eq_mul])]
      _ = (ENNReal.ofReal R ^ 2 * (NNReal.pi : ℝ≥0∞)).toReal *
            ∫ x : S, f x.1 ∂localBallProbability R := by rw [hm]
  let S := {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R}
  let : MeasureSpace S := Measure.Subtype.measureSpace
  let ν : Measure S := localBallProbability R
  have hν : IsProbabilityMeasure ν := by
    simpa [ν] using localBallProbability_isProbability hR
  let : IsProbabilityMeasure ν := hν
  let : IsProbabilityMeasure P := hX.1
  let σ : ℝ := -Real.log c
  let G := gaussianReal 0 ⟨σ,
    neg_nonneg.mpr (Real.log_nonpos (le_of_lt hc) hc1)⟩
  have hG : IsProbabilityMeasure G := by
    simpa [G, σ] using (ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0
      ⟨-Real.log c, neg_nonneg.mpr (Real.log_nonpos (le_of_lt hc) hc1)⟩)
  let : IsProbabilityMeasure G := hG
  let : IsProbabilityMeasure (P.prod G) := inferInstance
  let z : S → ℂ := fun x => x.1
  let weight : Fin m → S → ℝ := fun j x => f j (a + c • x.1)
  let varianceBase : S → ℝ≥0 := fun x =>
    (gaussianVariance P (fun ω => Xc ω x.1 r)).toNNReal
  let varianceTotal : S → ℝ≥0 := fun x =>
    (gaussianVariance P (fun ω => Xc ω (a + c • x.1) (r - Real.log c))).toNNReal
  let targetWick : Ω → Fin m → ℝ := fun ω j =>
    ∫ x, weight j x * Real.exp (γ * Xc ω (a + c • x.1) (r - Real.log c) -
      γ ^ 2 / 2 * (varianceTotal x : ℝ)) ∂ν
  let baseWick : Ω → Fin m → ℝ := fun ω j =>
    ∫ x, weight j x * Real.exp (γ * Xc ω x.1 r -
      γ ^ 2 / 2 * (varianceBase x : ℝ)) ∂ν
  let factor : Ω × ℝ → ℝ := fun p => Real.exp (γ * p.2 - γ ^ 2 / 2 * σ)
  let area := (ENNReal.ofReal R ^ 2 * (NNReal.pi : ℝ≥0∞)).toReal
  let k := c ^ 2 * area
  let A : (Fin m → ℝ) → Fin m → ℝ := fun v j => k * v j
  let targetVector : Ω → Fin m → ℝ := fun ω j =>
    ∫ x, f j x ∂regularizedGMC P Xc γ (r - Real.log c) ω
  let baseVector : Ω → Fin m → ℝ := fun ω j =>
    ∫ x, f j (a + c • x) ∂regularizedGMC P Xc γ r ω
  have himage : (fun x => a + c • x) '' Metric.closedBall (0 : ℂ) R =
      Metric.closedBall a (c * R) := complex_affine_image_closedBall hc
  have hfzeroTarget (j : Fin m) := boundedContinuousFunction_eq_zero_off_tsupport_subset (f j)
      (Metric.closedBall a (c * R)) (hf_support j)
  have hfzeroBase j : ∀ x, x ∉ Metric.closedBall (0 : ℂ) R →
      f j (a + c • x) = 0 := by
    intro x hx
    apply hfzeroTarget j
    intro hy
    obtain ⟨y, hyball, hyEq⟩ := (show a + c • x ∈ (fun y : ℂ => a + c • y) '' Metric.closedBall (0 : ℂ) R by rw [himage]; exact hy)
    have hxy : x = y := (show Function.Injective (fun x => a + c • x) by intro x y hxy; exact (smul_right_injective ℂ hc.ne') (add_left_cancel hxy)) (by simpa using hyEq.symm)
    exact hx (hxy ▸ hyball)
  have hweightMeas : ∀ j, Measurable (weight j) := by
    intro j
    dsimp [weight]
    fun_prop
  have hweightInt : ∀ j, Integrable (weight j) ν := by
    intro j
    refine (integrable_const ‖f j‖).mono' (hweightMeas j).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (by intro x; exact (f j).norm_coe_le_norm (a + c • x.1))
  have hfieldBase := (hXc.1 r).comp (by
      dsimp [S]
      fun_prop : Measurable (fun p : Ω × S => (p.1, p.2.1)))
  have hfieldTotal := (hXc.1 (r - Real.log c)).comp (by
      dsimp [S]
      fun_prop : Measurable (fun p : Ω × S => (p.1, a + c • p.2.1)))
  have htargetMeas : Measurable targetWick := by
    apply measurable_pi_iff.2
    intro j
    exact (((hweightMeas j).comp measurable_snd).mul (Real.measurable_exp.comp ((measurable_const.mul hfieldTotal).sub (measurable_const.mul (measurable_coe_nnreal_real.comp (((measurable_real_toNNReal.comp (circleAverage_variance_measurable (P := P) Xc hXc.1 (r - Real.log c))).comp (by fun_prop : Measurable (fun x : S => a + c • x.1))).comp measurable_snd)))))).stronglyMeasurable.integral_prod_right'.measurable
  have : Measurable baseWick := by
    apply measurable_pi_iff.2
    intro j
    exact (show Measurable (fun p : Ω × S => weight j p.2 * Real.exp (γ * Xc p.1 p.2.1 r - γ ^ 2 / 2 * (varianceBase p.2 : ℝ))) by exact ((hweightMeas j).comp measurable_snd).mul (Real.measurable_exp.comp ((measurable_const.mul hfieldBase).sub (measurable_const.mul (measurable_coe_nnreal_real.comp (((measurable_real_toNNReal.comp (circleAverage_variance_measurable (P := P) Xc hXc.1 r)).comp (measurable_subtype_coe)).comp measurable_snd)))))).stronglyMeasurable.integral_prod_right'.measurable
  have : Measurable factor := by
    dsimp [factor]
    fun_prop
  have hAmeas : Measurable A := by
    dsimp [A]
    fun_prop
  have hbaseVar (x : S) : (varianceBase x : ℝ) =
      gaussianVariance P (fun ω => Xc ω x.1 r) := Real.coe_toNNReal _
      (circleAverage_gaussian_law_and_variance_nonneg P X hX Xc hXc x.1 r).2
  have htotalVar (x : S) : (varianceTotal x : ℝ) =
      gaussianVariance P (fun ω => Xc ω (a + c • x.1) (r - Real.log c)) := Real.coe_toNNReal _ (circleAverage_gaussian_law_and_variance_nonneg
      P X hX Xc hXc (a + c • x.1) (r - Real.log c)).2
  have htargetPoint ω j : targetVector ω j = A (targetWick ω) j := by
    let g : ℂ → ℝ := fun y => f j y * Real.exp
      (γ * Xc ω y (r - Real.log c) - γ ^ 2 / 2 *
        gaussianVariance P (fun ω' => Xc ω' y (r - Real.log c)))
    have hrawWickEq : (∫ x : S, f j (a + c • x.1) * Real.exp
        (γ * Xc ω (a + c • x.1) (r - Real.log c) - γ ^ 2 / 2 *
          gaussianVariance P (fun ω' => Xc ω' (a + c • x.1) (r - Real.log c))) ∂ν) =
        targetWick ω j := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp [targetWick, weight]
        change f j (a + c • x.1) * Real.exp
          (γ * Xc ω (a + c • x.1) (r - Real.log c) - γ ^ 2 / 2 *
            gaussianVariance P (fun ω' => Xc ω' (a + c • x.1) (r - Real.log c))) =
          f j (a + c • x.1) * Real.exp
            (γ * Xc ω (a + c • x.1) (r - Real.log c) -
              γ ^ 2 / 2 * (varianceTotal x : ℝ))
        rw [← htotalVar x]
    change (∫ x, f j x ∂regularizedGMC P Xc γ (r - Real.log c) ω) =
      A (targetWick ω) j
    rw [(regularizedGMC_test_integral_eq_local_wick P X hX Xc hXc γ (r - Real.log c) (Metric.closedBall a (c * R)) Metric.isClosed_closedBall.measurableSet (htargetUnit) (f j) (f j).continuous.measurable (hfzeroTarget j) ω)]
    exact (calc
      (∫ y in Metric.closedBall a (c * R), f j y * Real.exp
          (γ * Xc ω y (r - Real.log c) - γ ^ 2 / 2 *
            gaussianVariance P (fun ω' => Xc ω' y (r - Real.log c))) ∂volume) =
        c ^ 2 * (∫ x in Metric.closedBall (0 : ℂ) R, f j (a + c • x) * Real.exp
          (γ * Xc ω (a + c • x) (r - Real.log c) - γ ^ 2 / 2 *
            gaussianVariance P (fun ω' => Xc ω' (a + c • x) (r - Real.log c))) ∂volume) := by
              rw [← himage]
              simpa [(show (|(c ^ 2)⁻¹|)⁻¹ = c ^ 2 by rw [abs_of_pos (inv_pos.mpr (sq_pos_of_ne_zero hc.ne'))]; field_simp), g] using (complex_integral_affine_restrict hc.ne' (Metric.closedBall (0 : ℂ) R) (by rw [himage]; exact Metric.isClosed_closedBall.measurableSet) g (show Measurable g by dsimp [g]; exact (f j).continuous.measurable.mul <| Real.measurable_exp.comp ((measurable_const.mul ((hXc.1 (r - Real.log c)).comp (measurable_const.prodMk measurable_id))).sub (measurable_const.mul (circleAverage_variance_measurable (P := P) Xc hXc.1 (r - Real.log c))))))
      _ = c ^ 2 * (area * targetWick ω j) := by
            rw [(localBallProbability_integral_mul_area (fun x => f j (a + c • x) * Real.exp (γ * Xc ω (a + c • x) (r - Real.log c) - γ ^ 2 / 2 * gaussianVariance P (fun ω' => Xc ω' (a + c • x) (r - Real.log c))))), hrawWickEq]
      _ = A (targetWick ω) j := by
            dsimp [A, k]
            ring
    )
  have hbasePoint ω j : baseVector ω j = area * baseWick ω j := by
    have hrawWickEq : (∫ x : S, f j (a + c • x.1) * Real.exp
        (γ * Xc ω x.1 r - γ ^ 2 / 2 *
          gaussianVariance P (fun ω' => Xc ω' x.1 r)) ∂ν) = baseWick ω j := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp [baseWick, weight]
        change f j (a + c • x.1) * Real.exp
          (γ * Xc ω x.1 r - γ ^ 2 / 2 *
            gaussianVariance P (fun ω' => Xc ω' x.1 r)) =
          f j (a + c • x.1) * Real.exp
            (γ * Xc ω x.1 r - γ ^ 2 / 2 * (varianceBase x : ℝ))
        rw [← hbaseVar x]
    change (∫ x, f j (a + c • x) ∂regularizedGMC P Xc γ r ω) = area * baseWick ω j
    rw [(regularizedGMC_test_integral_eq_local_wick P X hX Xc hXc γ r (Metric.closedBall (0 : ℂ) R) Metric.isClosed_closedBall.measurableSet (hsourceUnit) (fun x => f j (a + c • x)) (by fun_prop) (hfzeroBase j) ω)]
    exact (calc
      (∫ x in Metric.closedBall (0 : ℂ) R, f j (a + c • x) * Real.exp
          (γ * Xc ω x r - γ ^ 2 / 2 *
            gaussianVariance P (fun ω' => Xc ω' x r)) ∂volume) =
        area * baseWick ω j := by rw [(localBallProbability_integral_mul_area (fun x => f j (a + c • x) * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * gaussianVariance P (fun ω' => Xc ω' x r)))), hrawWickEq]
    )
  have hshiftPoint : ∀ p : Ω × ℝ,
      A (fun j => factor p * baseWick p.1 j) =
        (fun j => c ^ 2 * factor p * baseVector p.1 j) := by
    intro p
    funext j
    rw [hbasePoint p.1 j]
    dsimp [A, k]
    ring
  change Measure.map targetVector P =
    Measure.map (fun p : Ω × ℝ => fun j =>
      c ^ 2 * Real.exp (γ * p.2 - γ ^ 2 / 2 * (-Real.log c)) * baseVector p.1 j)
      (P.prod G)
  rw [(show targetVector = fun ω => A (targetWick ω) by funext ω j; exact htargetPoint ω j)]
  change Measure.map (A ∘ targetWick) P = _
  rw [← (Measure.map_map hAmeas htargetMeas), (show Measure.map targetWick P = Measure.map (fun p : Ω × ℝ => fun j => factor p * baseWick p.1 j) (P.prod G) by simpa [targetWick, baseWick, factor, varianceBase, varianceTotal, σ, G, weight, z] using (circleAverage_affine_scaled_wick_integral_law X Xc hX hXc ν (a := a) (c := c) (r := r) (γ := γ) hc hc1 z (by dsimp [z, S]; exact measurable_subtype_coe) hsourceCut htargetCut weight hweightMeas (by intro j x; exact hf_nonneg j (a + c • x.1)) hweightInt))]
  change Measure.map A
      (Measure.map (fun p : Ω × ℝ => fun j => factor p * baseWick p.1 j) (P.prod G)) = _
  rw [(Measure.map_map hAmeas (show Measurable (fun p : Ω × ℝ => fun j => factor p * baseWick p.1 j) by fun_prop))]
  change Measure.map
      (fun p : Ω × ℝ => A (fun j => factor p * baseWick p.1 j)) (P.prod G) = _
  rw [(show (fun p : Ω × ℝ => A (fun j => factor p * baseWick p.1 j)) = (fun p => fun j => c ^ 2 * Real.exp (γ * p.2 - γ ^ 2 / 2 * (-Real.log c)) * baseVector p.1 j) by funext p j; rw [hshiftPoint p])]

end DOZZ.Proofs
