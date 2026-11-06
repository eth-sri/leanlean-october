/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.RootedFiniteCutoffJoint
public import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
public import DOZZ.GMC.Moments.ReferenceFinite
public import DOZZ.GMC.Annulus.WeightedShell
public import DOZZ.GMC.CirclePotential
public import DOZZ.GMC.Moments.CircleScaleWick
public import DOZZ.GMC.Moments.ExactScale

/-!
# Finite-cutoff positive moment rooting

The Gaussian tilt is applied before taking the GMC limit. At every cutoff, multiplying
by one copy of the mass turns the order-p moment into an integral of order-(p-1)
inserted masses. This is the root-positive identity used by the sharp moment induction;
no limiting rooted GMC identity or weighted moment-existence input is used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- The Wick density without the deterministic equator reference density. -/
noncomputable def gmcCircleWickDensity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ)
    (γ r : ℝ) (ω : Ω) (x : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P))

/-- The Wick density is jointly measurable in the sample and spatial coordinate. -/
theorem measurable_gmcCircleWickDensity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P] (X : Ω → Distr)
    Xc (hXc : IsCircleAverage P X Xc) γ r :
    Measurable (fun q : Ω × ℂ => gmcCircleWickDensity P Xc γ r q.1 q.2) := by
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((measurable_const.mul (hXc.1 r)).sub (measurable_const.mul ((show Measurable (fun x => ∫ ω', Xc ω' x r ^ 2 ∂P) by exact (((hXc.1 r).comp measurable_swap).pow_const 2).stronglyMeasurable.integral_prod_right.measurable).comp measurable_snd))))

/-- The actual cutoff measure `DOZZ.regularizedGMC` is the reference measure weighted by the Wick
density. -/
theorem regularizedGMC_eq_reference_withDensity_PositiveRoot
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P] (X : Ω → Distr)
    Xc (hXc : IsCircleAverage P X Xc) γ r ω :
    regularizedGMC P Xc γ r ω =
      gmcReferenceMeasure.withDensity (gmcCircleWickDensity P Xc γ r ω) := by
  have hW : Measurable (gmcCircleWickDensity P Xc γ r ω) :=
    (measurable_gmcCircleWickDensity P X Xc hXc γ r).comp (f := fun x => (ω, x))
      (measurable_const.prodMk measurable_id)
  have hρ : Measurable (fun x => ENNReal.ofReal (normPlus x ^ (-4 : ℝ))) := by
    have : Measurable normPlus := measurable_const.max measurable_norm
    fun_prop
  rw [gmcReferenceMeasure, ← withDensity_mul volume hρ hW, regularizedGMC]
  congr 1
  funext x
  change ENNReal.ofReal (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P) *
      normPlus x ^ (-4 : ℝ)) = ENNReal.ofReal (normPlus x ^ (-4 : ℝ)) *
        gmcCircleWickDensity P Xc γ r ω x
  rw [gmcCircleWickDensity, ENNReal.ofReal_mul (Real.exp_nonneg _)]
  exact mul_comm _ _

/-- Cutoff mass on a Borel set is the actual reference integral of its Wick density. -/
theorem regularizedGMC_mass_eq_wick_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P] (X : Ω → Distr)
    Xc (hXc : IsCircleAverage P X Xc) γ r
    O (hO : MeasurableSet O) ω :
    regularizedGMC P Xc γ r ω O = ∫⁻ x in O, gmcCircleWickDensity P Xc γ r ω x ∂gmcReferenceMeasure := by
  rw [regularizedGMC_eq_reference_withDensity_PositiveRoot P X Xc hXc γ r ω, withDensity_apply _ hO]


/-- The equator reference measure is ordinary planar volume on every Borel unit subchart. -/
theorem gmcReferenceMeasure_restrict_unit_chart O (hO : MeasurableSet O)
    (hunit : ∀ x ∈ O, ‖x‖ ≤ 1) :
    gmcReferenceMeasure.restrict O = (volume : Measure ℂ).restrict O := by
  rw [gmcReferenceMeasure, restrict_withDensity hO]
  have he : (fun x => ENNReal.ofReal (normPlus x ^ (-4 : ℝ))) =ᵐ[volume.restrict O]
      fun _ => (1 : ℝ≥0∞) := by
    filter_upwards [ae_restrict_mem hO] with x hx
    have hn : normPlus x = 1 := max_eq_left (hunit x hx)
    simp only [hn, Real.one_rpow, ENNReal.ofReal_one]
  rw [withDensity_congr_ae he]
  change (volume.restrict O).withDensity 1 = volume.restrict O
  exact withDensity_one



/-- The source's uniform bounded covariance remainder on a compact spatial chart. -/
noncomputable def gmcCircleChartRemainder (R : ℝ) : ℝ := Real.log 3 + 2 * Real.log (1 + R)

/-- The remainder is nonnegative on the actual radius domain. -/
theorem gmcCircleChartRemainder_nonneg {R} (hR : 0 ≤ R) :
    0 ≤ gmcCircleChartRemainder R := by
  exact add_nonneg (Real.log_nonneg (by norm_num))
    (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))

/-- The tilted cutoff covariance is bounded by the actual clipped singular kernel plus a
constant uniform in the cutoff. This includes same-center values at the clipped scale. -/
theorem gmcCircle_tilt_covariance_upper
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (hX : IsEquatorGFF P X) Xc (hXc : IsCircleAverage P X Xc)
    γ R r (hR : 0 ≤ R) (hr : 0 ≤ r) x u
    (hx : ‖x‖ ≤ R) (hu : ‖u‖ ≤ R) :
    γ * gaussianCovariance P (fun ω => Xc ω x r) (fun ω => γ * Xc ω u r) ≤
      γ ^ 2 * (Real.log (1 / max ‖x - u‖ (Real.exp (-r))) + gmcCircleChartRemainder R) := by
  have gmcCircle_tilt_covariance_scalar (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ) γ r x u : γ * gaussianCovariance P (fun ω => Xc ω x r) (fun ω => γ * Xc ω u r) = γ ^ 2 * gaussianCovariance P (fun ω => Xc ω x r) (fun ω => Xc ω u r) := by
    have he : gaussianCovariance P (fun ω => Xc ω x r) (fun ω => γ * Xc ω u r) =
        γ * gaussianCovariance P (fun ω => Xc ω x r) (fun ω => Xc ω u r) := by
      unfold gaussianCovariance
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all P (fun _ => by ring)
    rw [he]
    ring
  rw [gmcCircle_tilt_covariance_scalar, isCircleAverage_covariance P X hX Xc hXc x u r r]
  have h := abs_circleKernel_sub_log_le R hR x u hx hu r r hr hr
  simp only [max_self] at h
  have hupp := (abs_le.mp h).2
  change circleKernel x r u r - Real.log (1 / max ‖x - u‖ (Real.exp (-r))) ≤
    gmcCircleChartRemainder R at hupp
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg γ)
  change circleKernel x r u r ≤ _
  linarith only [hupp]




/-- Rooting and the deterministic clipped-kernel bound give the actual cutoff induction
inequality, with order `p-1` on the right. It is valid even before either side is finite. -/
theorem regularizedGMC_positive_moment_le_clipped
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (hX : IsEquatorGFF P X) Xc (hXc : IsCircleAverage P X Xc)
    (γ R r p : ℝ) (hR : 0 ≤ R) (hr : 0 ≤ r) (hp : 1 < p)
    O (hO : MeasurableSet O) (hchart : ∀ x ∈ O, ‖x‖ ≤ R) :
    (∫⁻ ω, (regularizedGMC P Xc γ r ω O) ^ p ∂P) ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * gmcCircleChartRemainder R * (p - 1))) *
        ∫⁻ u in O, ∫⁻ ω,
          (∫⁻ x in O, ENNReal.ofReal ((max ‖x - u‖ (Real.exp (-r))) ^ (-γ ^ 2))
            ∂regularizedGMC P Xc γ r ω) ^ (p - 1) ∂P ∂gmcReferenceMeasure := by
  have regularizedGMC_inserted_mass_le_clipped u (hu : ‖u‖ ≤ R) ω : (((regularizedGMC P Xc γ r ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * gaussianCovariance P (fun ω' => Xc ω' x r) (fun ω' => γ * Xc ω' u r))))) O) ≤ ENNReal.ofReal (Real.exp (γ ^ 2 * gmcCircleChartRemainder R)) * ∫⁻ x in O, ENNReal.ofReal ((max ‖x - u‖ (Real.exp (-r))) ^ (-γ ^ 2)) ∂regularizedGMC P Xc γ r ω := by
    have gmcCircle_tilt_weight_upper x u (hx : ‖x‖ ≤ R) (hu : ‖u‖ ≤ R) : ENNReal.ofReal (Real.exp (γ * gaussianCovariance P (fun ω => Xc ω x r) (fun ω => γ * Xc ω u r))) ≤ ENNReal.ofReal (Real.exp (γ ^ 2 * gmcCircleChartRemainder R) * (max ‖x - u‖ (Real.exp (-r))) ^ (-γ ^ 2)) := by
      exact (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (gmcCircle_tilt_covariance_upper P X hX Xc hXc γ R r hR hr x u hx hu))).trans_eq
          (congrArg ENNReal.ofReal (by rw [Real.rpow_def_of_pos ((Real.exp_pos _).trans_le (le_max_right _ _)), one_div, Real.log_inv, ← Real.exp_add]; congr 1; ring))
    rw [withDensity_apply _ hO]
    calc
      _ ≤ ∫⁻ x in O, ENNReal.ofReal (Real.exp (γ ^ 2 * gmcCircleChartRemainder R)) *
          ENNReal.ofReal ((max ‖x - u‖ (Real.exp (-r))) ^ (-γ ^ 2))
            ∂regularizedGMC P Xc γ r ω := by
        apply setLIntegral_mono' hO
        intro x hx
        have h := gmcCircle_tilt_weight_upper x u (hchart x hx) hu
        rwa [ENNReal.ofReal_mul (Real.exp_nonneg _)] at h
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have regularizedGMC_positive_moment_root_identity : (∫⁻ ω, (regularizedGMC P Xc γ r ω O) ^ p ∂P) = ∫⁻ u in O, ∫⁻ ω, (((regularizedGMC P Xc γ r ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * gaussianCovariance P (fun ω' => Xc ω' x r) (fun ω' => γ * Xc ω' u r))))) O) ^ (p - 1) ∂P ∂gmcReferenceMeasure := by
    let _ := hX.1
    let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
    let W := gmcCircleWickDensity P Xc γ r
    let T : Ω → ℝ≥0∞ := fun ω => regularizedGMC P Xc γ r ω O
    have hpoint ω : (T ω) ^ p =
        ∫⁻ u in O, W ω u * (T ω) ^ (p - 1) ∂gmcReferenceMeasure := by
      have hW : Measurable (W ω) :=
        (measurable_gmcCircleWickDensity P X Xc hXc γ r).comp (f := fun x => (ω, x))
          (measurable_const.prodMk measurable_id)
      rw [lintegral_mul_const'' _ hW.aemeasurable, ← regularizedGMC_mass_eq_wick_lintegral P X Xc hXc γ r O hO ω]
      change (T ω) ^ p = T ω * (T ω) ^ (p - 1)
      calc
        _ = (T ω) ^ (1 + (p - 1)) := by congr 1; ring
        _ = (T ω) ^ (1 : ℝ) * (T ω) ^ (p - 1) :=
          ENNReal.rpow_add_of_nonneg 1 (p - 1) (by norm_num) (by linarith)
        _ = _ := by rw [ENNReal.rpow_one]
    calc
      _ = ∫⁻ ω, ∫⁻ u in O, W ω u * (T ω) ^ (p - 1) ∂gmcReferenceMeasure ∂P :=
        lintegral_congr hpoint
      _ = ∫⁻ u in O, ∫⁻ ω, W ω u * (T ω) ^ (p - 1) ∂P ∂gmcReferenceMeasure :=
        lintegral_lintegral_swap (show Measurable (fun q : Ω × ℂ => W q.1 q.2 * (T q.1) ^ (p - 1)) by exact (measurable_gmcCircleWickDensity P X Xc hXc γ r).mul (ENNReal.continuous_rpow_const.measurable.comp (((Measure.measurable_coe hO).comp (regularizedGMC_measurable P X hX Xc hXc γ r)).comp measurable_fst))).aemeasurable
      _ = _ := by
        apply lintegral_congr
        intro u
        exact regularizedGMC_joint_circle_tilt P X hX Xc hXc γ r u
          (fun _ μ => (μ O) ^ (p - 1)) (ENNReal.continuous_rpow_const.measurable.comp ((Measure.measurable_coe hO).comp measurable_snd))
  rw [regularizedGMC_positive_moment_root_identity]
  have hq : 0 ≤ p - 1 := by linarith
  calc
    _ ≤ ∫⁻ u in O, ∫⁻ ω,
        ENNReal.ofReal (Real.exp (γ ^ 2 * gmcCircleChartRemainder R * (p - 1))) *
          (∫⁻ x in O, ENNReal.ofReal ((max ‖x - u‖ (Real.exp (-r))) ^ (-γ ^ 2))
            ∂regularizedGMC P Xc γ r ω) ^ (p - 1) ∂P ∂gmcReferenceMeasure := by
      apply setLIntegral_mono' hO
      intro u hu
      apply lintegral_mono
      intro ω
      have h := ENNReal.rpow_le_rpow
        (regularizedGMC_inserted_mass_le_clipped
          u (hchart u hu) ω) hq
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq,
        ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul] at h
      exact h
    _ = _ := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The actual circle variance obeys the diagonal clipped-kernel estimate. -/
theorem gmcCircle_variance_le_cutoff_chart
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (hX : IsEquatorGFF P X) Xc (hXc : IsCircleAverage P X Xc)
    R r (hR : 0 ≤ R) (hr : 0 ≤ r) x (hx : ‖x‖ ≤ R) :
    gaussianVariance P (fun ω => Xc ω x r) ≤ r + gmcCircleChartRemainder R := by
  simpa only [one_mul, one_pow, sub_self, norm_zero,
    max_eq_right (Real.exp_nonneg _), one_div, Real.log_inv, Real.log_exp,
    neg_neg, gaussianVariance] using (gmcCircle_tilt_covariance_upper P X hX Xc hXc 1 R r hR hr x x hx hx)

/-- A bounded cutoff range therefore has one uniform variance bound on the entire chart. -/
theorem gmcCircle_variance_le_coarse_chart
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (hX : IsEquatorGFF P X) Xc (hXc : IsCircleAverage P X Xc)
    R r T (hR : 0 ≤ R) (hr : 0 ≤ r) (hrT : r ≤ T)
    x (hx : ‖x‖ ≤ R) :
    gaussianVariance P (fun ω => Xc ω x r) ≤ T + gmcCircleChartRemainder R :=
  (gmcCircle_variance_le_cutoff_chart P X hX Xc hXc R r hR hr x hx).trans
    (add_le_add hrT le_rfl)

/-- Every real power of an actual circle Wick density has the exact Gaussian expectation.
This includes inverse powers, since a finite-cutoff exponential is strictly positive. -/
theorem gmcCircleWickDensity_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (hX : IsEquatorGFF P X) Xc (hXc : IsCircleAverage P X Xc)
    (γ r p : ℝ) x :
    (∫⁻ ω, (gmcCircleWickDensity P Xc γ r ω x) ^ p ∂P) =
      ENNReal.ofReal (Real.exp (γ ^ 2 * (p ^ 2 - p) / 2 *
        gaussianVariance P (fun ω => Xc ω x r))) := by
  obtain ⟨hLaw, hv⟩ := circleAverage_gaussian_law_and_variance_nonneg P X hX Xc hXc x r
  let V := gaussianVariance P (fun ω => Xc ω x r)
  have heint : Integrable (fun ω => Real.exp ((p * γ) * Xc ω x r)) P := by
    have hm : Integrable (fun t => Real.exp ((p * γ) * t))
        (P.map (fun ω => Xc ω x r)) := by
      rw [hLaw.map_eq]
      exact integrable_exp_mul_gaussianReal _
    exact (integrable_map_measure hm.aestronglyMeasurable hLaw.aemeasurable).mp hm
  have hint : Integrable (fun ω => Real.exp
      ((γ * Xc ω x r - γ ^ 2 / 2 * V) * p)) P := by
    convert heint.const_mul (Real.exp (-γ ^ 2 / 2 * V * p)) using 1
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  have hmgf := gaussian_exponential_moment_of_hasLaw hLaw (p * γ)
  rw [Real.coe_toNNReal _ hv] at hmgf
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp ((γ * Xc ω x r - γ ^ 2 / 2 * V) * p)) ∂P := by
      apply lintegral_congr
      intro ω
      rw [gmcCircleWickDensity, (show (∫ ω, Xc ω x r ^ 2 ∂P) = V by simp only [V, gaussianVariance, gaussianCovariance, pow_two]), ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
        ← Real.exp_mul]
    _ = ENNReal.ofReal (∫ ω, Real.exp ((γ * Xc ω x r - γ ^ 2 / 2 * V) * p) ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all P (fun _ => Real.exp_nonneg _))).symm
    _ = ENNReal.ofReal (Real.exp (-γ ^ 2 / 2 * V * p) *
        ∫ ω, Real.exp ((p * γ) * Xc ω x r) ∂P) := by
      congr 1
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all P (fun ω => by
        change Real.exp ((γ * Xc ω x r - γ ^ 2 / 2 * V) * p) =
          Real.exp (-γ ^ 2 / 2 * V * p) * Real.exp ((p * γ) * Xc ω x r)
        rw [← Real.exp_add]
        congr 1
        ring)
    _ = _ := by
      rw [hmgf, ← Real.exp_add]
      congr 2
      dsimp [V]
      ring


/-- Convex powers of the Wick density have one common bound over any coarse cutoff range.
The condition on the order is exactly the sign needed to use the upper variance estimate. -/
theorem gmcCircleWickDensity_coarse_convex_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (hX : IsEquatorGFF P X) Xc (hXc : IsCircleAverage P X Xc)
    (γ R T p : ℝ) (hR : 0 ≤ R) (hp : p ≤ 0 ∨ 1 ≤ p)
    r (hr : 0 ≤ r) (hrT : r ≤ T) x (hx : ‖x‖ ≤ R) :
    (∫⁻ ω, (gmcCircleWickDensity P Xc γ r ω x) ^ p ∂P) ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * (p ^ 2 - p) / 2 *
        (T + gmcCircleChartRemainder R))) := by
  rw [gmcCircleWickDensity_moment P X hX Xc hXc γ r p x]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left
      (gmcCircle_variance_le_coarse_chart P X hX Xc hXc R r T hR hr hrT x hx) (by exact div_nonneg (mul_nonneg (sq_nonneg γ) (by rcases hp with hp | hp <;> nlinarith [sq_nonneg p])) (by norm_num))))


end DOZZ.Proofs
