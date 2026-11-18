module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Moments.SubGaussian
public import NearlyMinimax.ActualSeparatedPacket
public import NearlyMinimax.CardinalInterpolationBias
public import NearlyMinimax.LowSmoothnessVariance
public import NearlyMinimax.Risk
public import NearlyMinimax.ScoreSupport
public import NearlyMinimax.TernaryMeasure

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped BigOperators ENNReal NNReal
namespace NearlyMinimax

-- ============================================================================
-- 1. Cardinal Weighted Bounds, Coefficient Bounds, Band L2, and Continuity
-- ============================================================================

section CardinalBandCluster
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem integral_square_le_weight_mass_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (h w g : α → ℝ) (hh : Integrable h μ)
    (hw : Integrable w μ) (hg : Integrable g μ)
    (hwn : ∀ᵐ x ∂μ, 0 ≤ w x) (hgn : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hdom : ∀ᵐ x ∂μ, (h x) ^ 2 ≤ w x * g x) :
    (∫ x, h x ∂μ) ^ 2 ≤ (∫ x, w x ∂μ) * (∫ x, g x ∂μ) := by
  have hws : AEStronglyMeasurable (fun x => Real.sqrt (w x)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hw.aestronglyMeasurable
  have hgs : AEStronglyMeasurable (fun x => Real.sqrt (g x)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hg.aestronglyMeasurable
  have hew : (fun x => Real.sqrt (w x) ^ 2) =ᵐ[μ] w := hwn.mono fun _ => Real.sq_sqrt
  have heg : (fun x => Real.sqrt (g x) ^ 2) =ᵐ[μ] g := hgn.mono fun _ => Real.sq_sqrt
  have hwL : MemLp (fun x => Real.sqrt (w x)) 2 μ := (memLp_two_iff_integrable_sq hws).mpr (hw.congr hew.symm)
  have hgL : MemLp (fun x => Real.sqrt (g x)) 2 μ := (memLp_two_iff_integrable_sq hgs).mpr (hg.congr heg.symm)
  have hprod := memLp_one_iff_integrable.mp (hwL.fun_mul hgL)
  have hpoint : (fun x => |h x|) ≤ᵐ[μ] fun x => Real.sqrt (w x) * Real.sqrt (g x) := by
    filter_upwards [hwn, hgn, hdom] with x hx hy hz
    refine (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp ?_
    simpa only [sq_abs, mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy] using hz
  have hcs := integral_cauchy_schwarz μ _ _ hwL hgL
  rw [integral_congr_ae hew, integral_congr_ae heg] at hcs
  have hW : 0 ≤ ∫ x, w x ∂μ := integral_nonneg_of_ae hwn
  have hG : 0 ≤ ∫ x, g x ∂μ := integral_nonneg_of_ae hgn
  have hbound : |∫ x, h x ∂μ| ≤ Real.sqrt (∫ x, w x ∂μ) * Real.sqrt (∫ x, g x ∂μ) :=
    ((by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm h : |∫ x, h x ∂μ| ≤ ∫ x, |h x| ∂μ).trans
      (integral_mono_ae hh.abs hprod hpoint)).trans ((le_abs_self _).trans hcs)
  simpa only [sq_abs, mul_pow, Real.sq_sqrt hW, Real.sq_sqrt hG] using
    (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hbound

def spatialMatrixL1 {d D : ℕ} (A : HighFrameIndex d D → HighFrameIndex d D → ℝ) : ℝ :=
  ∑ β, ∑ β', |A β β'|

theorem spatial_matrix_l1_nonnegative {d D : ℕ} (A : HighFrameIndex d D → HighFrameIndex d D → ℝ) :
    0 ≤ spatialMatrixL1 A := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma spatial_cardinal_scale_nonnegative {d n : ℕ} (i : Fin n) (lam : ℝ)
    (U : Fin n → Covariate d) (t : SpatialScaleVector i) (ht : t ∈ Ici 0) :
    0 ≤ spatialCardinalScale lam (spatialScaleExtend i t) U i := by
  rw [spatial_cardinal_scale_product]
  exact Finset.prod_nonneg fun j _ => mul_nonneg (mul_nonneg (ht j) (sq_nonneg _)) (Real.exp_pos _).le

lemma spatial_centered_matrix_l1_square_le_weight_scale {d n D : ℕ}
    (i : Fin n) (lam : ℝ) (U : Fin n → Covariate d) (hU : ∀ l r, |U l r| ≤ 2)
    (t : SpatialScaleVector i) (ht : t ∈ Ici 0) :
    (spatialMatrixL1 (spatialCenteredCardinalMatrix (D := D) i lam U t)) ^ 2 ≤
      spatialCardinalWeight lam (spatialScaleExtend i t) U i *
        ((100 * (d : ℝ)) ^ (2 * Fintype.card (SpatialScaleIndex i)) *
          spatialCardinalScale lam (spatialScaleExtend i t) U i) := by
  classical
  have haff {x y : Covariate d} (hy : ∀ r, |y r| ≤ 2) :
      (frameCoefficientL1 (spatialCardinalAffine x y)) ^ 2 ≤ 100 * (d : ℝ) * spatialSquaredDistance x y := by
    let expn (z : Fin d × Bool) : Fin d →₀ ℕ := if z.2 then 0 else Finsupp.single z.1 1
    let coef (z : Fin d × Bool) : ℝ := if z.2 then (y z.1 - x z.1) * y z.1 else -8 * (y z.1 - x z.1)
    have hmon : spatialCardinalAffine x y = ∑ z : Fin d × Bool, MvPolynomial.monomial (expn z) (coef z) := by
      rw [Fintype.sum_prod_type]; unfold spatialCardinalAffine
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Fintype.sum_bool]
      simp only [expn, coef, Bool.false_eq_true, ite_false, ite_true]
      rw [← MvPolynomial.C_apply, ← MvPolynomial.C_mul_X_eq_monomial,
        show (-8 : ℝ) * (y r - x r) = -(8 * (y r - x r)) by ring, map_neg]; ring
    have hb : frameCoefficientL1 (spatialCardinalAffine x y) ≤ 10 * ∑ r, |y r - x r| := by
      rw [hmon]; refine (frameCoefficientL1_sum_monomial_le _ _).trans ?_
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_le_sum fun r _ => ?_
      rw [Fintype.sum_bool]
      simp only [coef, Bool.false_eq_true, ite_false, ite_true, abs_mul]
      norm_num only [abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 8 by norm_num)]
      linarith [mul_le_mul_of_nonneg_left (hy r) (abs_nonneg (y r - x r))]
    have hs := (sq_le_sq₀ (frameCoefficientL1_nonneg _) (by positivity)).mpr hb
    have hsum := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := fun r => |y r - x r|)
    simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at hsum
    change (∑ r, |y r - x r|) ^ 2 ≤ (d : ℝ) * spatialSquaredDistance x y at hsum
    nlinarith
  have hpoly : (frameCoefficientL1 (spatialCardinalPolynomial U i)) ^ 2 ≤
      (100 * (d : ℝ)) ^ Fintype.card (SpatialScaleIndex i) *
        ∏ j : SpatialScaleIndex i, spatialSquaredDistance (U i) (U j.val) := by
    rw [spatial_cardinal_polynomial_scale_product]
    have hp := frameCoefficientL1_prod Finset.univ fun j : SpatialScaleIndex i => spatialCardinalAffine (U i) (U j.val)
    calc
      _ ≤ (∏ j : SpatialScaleIndex i, frameCoefficientL1 (spatialCardinalAffine (U i) (U j.val))) ^ 2 :=
        (sq_le_sq₀ (frameCoefficientL1_nonneg _) (Finset.prod_nonneg fun _ _ => frameCoefficientL1_nonneg _)).mpr hp
      _ = ∏ j : SpatialScaleIndex i, (frameCoefficientL1 (spatialCardinalAffine (U i) (U j.val))) ^ 2 := by
        rw [Finset.prod_pow]
      _ ≤ ∏ j : SpatialScaleIndex i, 100 * (d : ℝ) * spatialSquaredDistance (U i) (U j.val) :=
        Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) fun j _ => haff (hU j.val)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hn := spatial_cardinal_scale_nonnegative i lam U t ht
  have hb := ((sq_le_sq₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) (frameCoefficientL1_nonneg _)).mpr
    (highFrameCoefficients_sum_abs_le (D := D) (spatialCardinalPolynomial U i))).trans hpoly
  have hl1 : spatialMatrixL1 (spatialCenteredCardinalMatrix (D := D) i lam U t) =
      spatialCardinalScale lam (spatialScaleExtend i t) U i *
        (∑ β : HighFrameIndex d D, |highFrameCoefficients (spatialCardinalPolynomial U i) β|) ^ 2 := by
    unfold spatialMatrixL1 spatialCenteredCardinalMatrix
    simp_rw [abs_mul, abs_of_nonneg hn]
    rw [show (∑ β : HighFrameIndex d D, ∑ β' : HighFrameIndex d D,
        spatialCardinalScale lam (spatialScaleExtend i t) U i *
          |highFrameCoefficients (spatialCardinalPolynomial U i) β| *
          |highFrameCoefficients (spatialCardinalPolynomial U i) β'|) =
        spatialCardinalScale lam (spatialScaleExtend i t) U i *
          (∑ β : HighFrameIndex d D, |highFrameCoefficients (spatialCardinalPolynomial U i) β|) *
          (∑ β : HighFrameIndex d D, |highFrameCoefficients (spatialCardinalPolynomial U i) β|) by
      simp_rw [← Finset.mul_sum]; rw [← Finset.sum_mul, ← Finset.mul_sum]]
    ring
  rw [hl1]
  have hprod : 0 ≤ ∏ j : SpatialScaleIndex i, spatialSquaredDistance (U i) (U j.val) :=
    Finset.prod_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ((sq_le_sq₀ (mul_nonneg hn (sq_nonneg _)) (mul_nonneg hn (mul_nonneg (by positivity) hprod))).mpr
    (mul_le_mul_of_nonneg_left hb hn)).trans_eq ?_
  have hw : spatialCardinalWeight lam (spatialScaleExtend i t) U i =
      spatialCardinalScale lam (spatialScaleExtend i t) U i *
        (∏ j : SpatialScaleIndex i, spatialSquaredDistance (U i) (U j.val)) ^ 2 := by
    rw [spatial_cardinal_weight_scale_product, spatial_cardinal_scale_product, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun _ _ => ?_
    unfold spatialUnaryWeight; rw [mul_pow]; ring
  rw [hw, show (100 * (d : ℝ)) ^ (2 * Fintype.card (SpatialScaleIndex i)) =
    ((100 * (d : ℝ)) ^ Fintype.card (SpatialScaleIndex i)) ^ 2 by rw [← pow_mul, Nat.mul_comm]]
  ring

abbrev CardinalBandMark (d n : ℕ) := Bool × CardinalSeparatedMark d n

def cardinalBandMeasure (d n : ℕ) (L T : ℝ) : Measure (CardinalBandMark d n) :=
  Measure.map (fun z => (false, z)) (cardinalSeparatedMeasure d n T) +
    Measure.map (fun z => (true, z)) (cardinalSeparatedMeasure d n (max 1 L))

def cardinalBandAmplitude {d n D : ℕ} (lam : ℝ) (z : CardinalBandMark d n)
    (β β' : HighFrameIndex d D) : ℝ :=
  if z.1 then -cardinalSeparatedAmplitude lam z.2 β β' else cardinalSeparatedAmplitude lam z.2 β β'

def cardinalBandFactor {d n : ℕ} (lam : ℝ) (z : CardinalBandMark d n)
    (l : Fin n) (x : Covariate d) : ℝ := cardinalSeparatedFactor lam z.2 l x

theorem cardinal_band_mark_standardBorel (d n : ℕ) : StandardBorelSpace (CardinalBandMark d n) := by
  letI := cardinal_separated_mark_standardBorel d n
  infer_instance

theorem cardinal_band_measure_finite (d n : ℕ) (L : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    IsFiniteMeasure (cardinalBandMeasure d n L T) := by
  letI := cardinal_separated_measure_finite d n hT
  letI := cardinal_separated_measure_finite d n (le_max_left 1 L)
  unfold cardinalBandMeasure; infer_instance

theorem cardinal_band_amplitude_measurable {d n D : ℕ} (lam : ℝ) (β β' : HighFrameIndex d D) :
    Measurable fun z : CardinalBandMark d n => cardinalBandAmplitude lam z β β' :=
  Measurable.ite (measurable_fst (measurableSet_singleton true))
    ((cardinal_separated_amplitude_measurable lam β β').comp measurable_snd).neg
    ((cardinal_separated_amplitude_measurable lam β β').comp measurable_snd)

theorem cardinal_band_factor_measurable {d n : ℕ} (lam : ℝ) (l : Fin n) (x : Covariate d) :
    Measurable fun z : CardinalBandMark d n => cardinalBandFactor lam z l x :=
  (cardinal_separated_factor_measurable lam l x).comp measurable_snd

theorem cardinal_band_factor_abs_le_one {d n : ℕ} (lam : ℝ) (z : CardinalBandMark d n)
    (l : Fin n) (x : Covariate d) (hx : ∀ r, |x r| ≤ 2) : |cardinalBandFactor lam z l x| ≤ 1 :=
  cardinal_separated_factor_abs_le_one lam z.2 l x hx

lemma cardinal_band_integral_eq_copies {d n : ℕ} (L T : ℝ)
    (f : CardinalBandMark d n → ℝ) (hf : Measurable f)
    (hT : Integrable (fun z => f (false, z)) (cardinalSeparatedMeasure d n T))
    (hL : Integrable (fun z => f (true, z)) (cardinalSeparatedMeasure d n (max 1 L))) :
    Integrable f (cardinalBandMeasure d n L T) ∧
      (∫ z, f z ∂cardinalBandMeasure d n L T) =
        (∫ z, f (false, z) ∂cardinalSeparatedMeasure d n T) +
          (∫ z, f (true, z) ∂cardinalSeparatedMeasure d n (max 1 L)) := by
  have hmF : Measurable fun z : CardinalSeparatedMark d n => (false, z) := by fun_prop
  have hmL : Measurable fun z : CardinalSeparatedMark d n => (true, z) := by fun_prop
  have hiF := (integrable_map_measure hf.aestronglyMeasurable hmF.aemeasurable).mpr hT
  have hiL := (integrable_map_measure hf.aestronglyMeasurable hmL.aemeasurable).mpr hL
  refine ⟨integrable_add_measure.mpr ⟨hiF, hiL⟩, ?_⟩
  unfold cardinalBandMeasure
  rw [integral_add_measure hiF hiL,
    integral_map hmF.aemeasurable hf.aestronglyMeasurable,
    integral_map hmL.aemeasurable hf.aestronglyMeasurable]

lemma cardinal_band_cost_eq {d n D : ℕ} (lam : ℝ) (z : CardinalBandMark d n) :
    separatedMatrixCost (cardinalBandAmplitude (D := D) lam) z =
      separatedMatrixCost (cardinalSeparatedAmplitude (D := D) lam) z.2 := by
  unfold separatedMatrixCost cardinalBandAmplitude
  cases z.1 <;> simp only [Bool.false_eq_true, ite_false, ite_true, abs_neg]

theorem cardinal_band_cost_integrable {d n D : ℕ} (lam L : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    Integrable (separatedMatrixCost (cardinalBandAmplitude (D := D) lam)) (cardinalBandMeasure d n L T) :=
  have hm : Measurable (separatedMatrixCost (cardinalBandAmplitude (d := d) (n := n) (D := D) lam)) :=
    Finset.measurable_fun_sum _ fun β _ => Finset.measurable_fun_sum _ fun β' _ =>
      (cardinal_band_amplitude_measurable lam β β').abs
  (cardinal_band_integral_eq_copies L T _ hm
    (by simpa only [cardinal_band_cost_eq] using cardinal_separated_cost_integrable (D := D) lam hT)
    (by simpa only [cardinal_band_cost_eq] using cardinal_separated_cost_integrable (D := D) lam (le_max_left 1 L))).1

theorem cardinal_band_cost_integral_le {d n D : ℕ} (hn : 2 ≤ n) (lam L : ℝ)
    {T : ℝ} (hT : 1 ≤ T) (hLT : L ≤ T) :
    (∫ z, separatedMatrixCost (cardinalBandAmplitude (D := D) lam) z ∂cardinalBandMeasure d n L T) ≤
      2 * (n : ℝ) * (1024 * |lam| * (d : ℝ) ^ 2) ^ (n - 1) * T ^ 2 * (1 + Real.log T) ^ (n - 2) := by
  have hm : Measurable (separatedMatrixCost (cardinalBandAmplitude (d := d) (n := n) (D := D) lam)) :=
    Finset.measurable_fun_sum _ fun β _ => Finset.measurable_fun_sum _ fun β' _ =>
      (cardinal_band_amplitude_measurable lam β β').abs
  rw [(cardinal_band_integral_eq_copies L T _ hm
    (by simpa only [cardinal_band_cost_eq] using cardinal_separated_cost_integrable (D := D) lam hT)
    (by simpa only [cardinal_band_cost_eq] using cardinal_separated_cost_integrable (D := D) lam (le_max_left 1 L))).2]
  simp_rw [cardinal_band_cost_eq]
  have hmax : max 1 L ≤ T := max_le hT hLT
  have hp : 0 < max 1 L := lt_of_lt_of_le one_pos (le_max_left 1 L)
  have hlog : 1 + Real.log (max 1 L) ≤ 1 + Real.log T := add_le_add le_rfl (Real.log_le_log hp hmax)
  have hlogn : 0 ≤ 1 + Real.log (max 1 L) := add_nonneg zero_le_one (Real.log_nonneg (le_max_left 1 L))
  have hsmall : (n : ℝ) * (1024 * |lam| * (d : ℝ) ^ 2) ^ (n - 1) * (max 1 L) ^ 2 *
      (1 + Real.log (max 1 L)) ^ (n - 2) ≤
      (n : ℝ) * (1024 * |lam| * (d : ℝ) ^ 2) ^ (n - 1) * T ^ 2 * (1 + Real.log T) ^ (n - 2) := by gcongr
  have h := add_le_add (cardinal_separated_cost_integral_le (d := d) (D := D) hn lam hT)
    ((cardinal_separated_cost_integral_le (d := d) (D := D) hn lam (le_max_left 1 L)).trans hsmall)
  convert h using 1 <;> ring

theorem spatial_scale_domain_empty_below_one {n : ℕ} (i : Fin n) {L : ℝ}
    (hL : 0 < L) (hL1 : L < 1) : spatialScaleDomain i L = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun t ht => by
    have hnn : 0 ≤ spatialScaleLogSum i t := by
      unfold spatialScaleLogSum
      exact Finset.sum_nonneg fun j _ => Real.log_nonneg (by linarith [le_max_left (0 : ℝ) (t j)])
    have hl := Real.log_neg hL hL1
    have hc : spatialScaleLogSum i t ≤ 2 * Real.log L := ht.2
    linarith

theorem integrated_cardinal_matrix_below_one_eq_zero {d n D : ℕ}
    (_i : Fin n) (lam : ℝ) {L : ℝ} (hL : 0 < L) (hL1 : L < 1)
    (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam L U β β' = 0 := by
  unfold integratedCardinalMatrix spatialScaleMeasure
  simp_rw [spatial_scale_domain_empty_below_one _ hL hL1, Measure.restrict_empty, integral_zero_measure]
  exact Finset.sum_const_zero

theorem integrated_cardinal_matrix_max_one {d n D : ℕ} (hn : 2 ≤ n)
    (lam : ℝ) {L : ℝ} (hL : 0 < L) (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam (max 1 L) U β β' = integratedCardinalMatrix lam L U β β' := by
  by_cases hL1 : 1 ≤ L
  · rw [max_eq_right hL1]
  · rw [max_eq_left (not_le.mp hL1).le, integrated_cardinal_matrix_one_eq_zero hn,
      integrated_cardinal_matrix_below_one_eq_zero ⟨0, by omega⟩ lam hL (not_le.mp hL1)]
    rfl

theorem integrated_cardinal_actual_band_separated_exact {d n D : ℕ} (hn : 2 ≤ n)
    (lam : ℝ) (hlam : 0 ≤ lam) {L T : ℝ} (hL : 0 < L) (hT : 1 ≤ T)
    (U : Fin n → Covariate d) (hU : ∀ l r, |U l r| ≤ 2) (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam T U β β' - integratedCardinalMatrix lam L U β β' =
      ∫ z, cardinalSeparatedSymmetricFactor lam z.2 U * cardinalBandAmplitude lam z β β'
        ∂cardinalBandMeasure d n L T := by
  rw [← integrated_cardinal_matrix_max_one hn lam hL U β β']
  have hsymM : Measurable fun z : CardinalSeparatedMark d n => cardinalSeparatedSymmetricFactor lam z U :=
    (Finset.measurable_fun_sum _ fun τ _ => Finset.measurable_fun_prod _ fun l _ =>
      cardinal_separated_factor_measurable lam l (U (τ l))).div_const _
  have hm : Measurable fun z : CardinalBandMark d n =>
      cardinalSeparatedSymmetricFactor lam z.2 U * cardinalBandAmplitude lam z β β' :=
    (hsymM.comp measurable_snd).mul (cardinal_band_amplitude_measurable lam β β')
  have hiT : Integrable (fun z => cardinalSeparatedSymmetricFactor lam z U *
      cardinalBandAmplitude lam (false, z) β β') (cardinalSeparatedMeasure d n T) := by
    simpa only [cardinalBandAmplitude, Bool.false_eq_true, ite_false] using
      cardinal_separated_symmetric_entry_integrable lam hT U hU β β'
  have hiL : Integrable (fun z => cardinalSeparatedSymmetricFactor lam z U *
      cardinalBandAmplitude lam (true, z) β β') (cardinalSeparatedMeasure d n (max 1 L)) := by
    have hh : Integrable (fun z => -(cardinalSeparatedSymmetricFactor lam z U *
        cardinalSeparatedAmplitude lam z β β')) (cardinalSeparatedMeasure d n (max 1 L)) :=
      (cardinal_separated_symmetric_entry_integrable lam (le_max_left 1 L) U hU β β').neg
    simpa only [cardinalBandAmplitude, ite_true, mul_neg] using hh
  rw [(cardinal_band_integral_eq_copies L T _ hm hiT hiL).2]
  simp only [cardinalBandAmplitude, Bool.false_eq_true, ite_false, ite_true, mul_neg, integral_neg]
  rw [← integrated_cardinal_symmetric_separated_exact lam hlam hT U hU β β',
    ← integrated_cardinal_symmetric_separated_exact lam hlam (le_max_left 1 L) U hU β β']
  ring

lemma spatial_cardinal_polynomial_coefficients_continuous {d n : ℕ}
    (i : Fin n) (β : Fin d →₀ ℕ) :
    Continuous fun U : Fin n → Covariate d => (spatialCardinalPolynomial U i).coeff β := by
  classical
  have hprod : ∀ (s : Finset (Fin n)),
      (∀ k ∈ s, ∀ γ, Continuous fun U : Fin n → Covariate d => (spatialCardinalAffine (U i) (U k)).coeff γ) →
      ∀ γ, Continuous fun U : Fin n → Covariate d => (∏ k ∈ s, spatialCardinalAffine (U i) (U k)).coeff γ := by
    intro s; induction s using Finset.induction_on with
    | empty => intro _ _; simp only [Finset.prod_empty]; exact continuous_const
    | @insert k s hk ih =>
      intro hP γ
      simp only [Finset.prod_insert hk, MvPolynomial.coeff_mul]
      exact continuous_finsetSum _ fun w _ =>
        (hP k (Finset.mem_insert_self _ _) w.1).mul (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)) w.2)
  unfold spatialCardinalPolynomial
  refine hprod ((Finset.univ : Finset (Fin n)).erase i) (fun j _ δ => ?_) β
  simp only [spatialCardinalAffine, MvPolynomial.coeff_sum, MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul]
  refine continuous_finsetSum _ fun r _ => Continuous.sub ?_ ?_
  · by_cases hδ : (0 : Fin d →₀ ℕ) = δ
    · simp only [MvPolynomial.coeff_C, hδ, ite_true]; fun_prop
    · simp only [MvPolynomial.coeff_C, hδ, ite_false]; exact continuous_const
  · exact (by fun_prop : Continuous fun U : Fin n → Covariate d => 8 * (U j r - U i r)).mul continuous_const

def spatialScaleIntegralConstant (d : ℕ) : ℝ :=
  (spatialInterpolationLambda d) ^ 2 * Real.exp (1 / 2) *
    (Real.sqrt (2 * Real.pi / spatialInterpolationLambda d)) ^ d

def anchoredCardinalScale {d n : ℕ} (i : Fin n) (lam : ℝ) (x : Covariate d)
    (t : SpatialScaleVector i) (Y : SpatialScaleIndex i → Covariate d) : ℝ :=
  spatialCardinalScale lam (spatialScaleExtend i t) (anchoredPatchConfiguration i x Y) i

lemma anchored_cardinal_scale_product_actual {d n : ℕ} (i : Fin n) (lam : ℝ) (x : Covariate d)
    (t : SpatialScaleVector i) (Y : SpatialScaleIndex i → Covariate d) :
    anchoredCardinalScale i lam x t Y = ∏ j : SpatialScaleIndex i,
      t j * lam ^ 2 * Real.exp (-(t j * lam * spatialSquaredDistance x (Y j))) := by
  unfold anchoredCardinalScale
  rw [spatial_cardinal_scale_product]
  simp_rw [anchored_configuration_same, anchored_configuration_other]

lemma anchored_cardinal_scale_continuous_actual {d n : ℕ} (i : Fin n) (lam : ℝ) (x : Covariate d) :
    Continuous fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalScale i lam x z.1 z.2 := by
  simp_rw [anchored_cardinal_scale_product_actual]
  unfold spatialSquaredDistance; fun_prop

lemma anchored_cardinal_band_scale_joint_integrable {d n : ℕ} (i : Fin n) {lam T : ℝ}
    (hlam : 0 ≤ lam) (hT : 1 ≤ T) (L : ℝ) (x : Covariate d) :
    Integrable (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalScale i lam x z.1 z.2)
      ((volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L)).prod (spatialPatchDesignMeasure i d)) := by
  letI := spatial_scale_measure_finite i T hT
  have hμ : volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L) ≤ spatialScaleMeasure i T :=
    Measure.restrict_mono_set volume Set.diff_subset
  letI : IsFiniteMeasure (volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L)) :=
    isFiniteMeasure_of_le (spatialScaleMeasure i T) hμ
  apply Integrable.of_bound (anchored_cardinal_scale_continuous_actual i lam x).aestronglyMeasurable
    ((T ^ 2 * lam ^ 2) ^ Fintype.card (SpatialScaleIndex i))
  have hae : ∀ᵐ z ∂((volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L)).prod
      (spatialPatchDesignMeasure i d)), z.1 ∈ spatialScaleDomain i T := by
    apply (Measure.ae_prod_iff_ae_ae ((spatial_scale_domain_isClosed i T).measurableSet.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem ((spatial_scale_domain_isClosed i T).measurableSet.diff
      (spatial_scale_domain_isClosed i L).measurableSet)] with t ht
    exact ae_of_all _ fun _ => ht.1
  filter_upwards [hae] with z hz
  rw [anchored_cardinal_scale_product_actual, Real.norm_eq_abs,
    abs_of_nonneg (Finset.prod_nonneg fun j _ => mul_nonneg (mul_nonneg (hz.1 j) (sq_nonneg _)) (Real.exp_pos _).le)]
  refine (Finset.prod_le_prod₀ (g := fun _ => T ^ 2 * lam ^ 2)
    (fun j _ => mul_nonneg (mul_nonneg (hz.1 j) (sq_nonneg _)) (Real.exp_pos _).le)
    fun j _ => ?_).trans_eq (by simp)
  have htj : 0 ≤ z.1 j := hz.1 j
  have hdist : 0 ≤ spatialSquaredDistance x (z.2 j) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have he : Real.exp (-(z.1 j * lam * spatialSquaredDistance x (z.2 j))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (mul_nonneg htj hlam) hdist))
  have hsmall := (spatial_scale_domain_subset_box i T hT hz).2 j
  exact (mul_le_mul_of_nonneg_left he (mul_nonneg htj (sq_nonneg _))).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_right (show z.1 j ≤ T ^ 2 by linarith) (sq_nonneg lam))

def centeredCardinalBandMatrix {d n D : ℕ} (i : Fin n) (lam L T : ℝ)
    (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) : ℝ :=
  ∫ t : SpatialScaleVector i in spatialScaleDomain i T \ spatialScaleDomain i L,
    spatialCenteredCardinalMatrix i lam U t β β'

def anchoredCenteredCardinalBandMatrix {d n D : ℕ} (i : Fin n) (lam L T : ℝ) (x : Covariate d)
    (Y : SpatialScaleIndex i → Covariate d) : HighFrameIndex d D → HighFrameIndex d D → ℝ :=
  centeredCardinalBandMatrix i lam L T (anchoredPatchConfiguration i x Y)

lemma centered_cardinal_band_matrix_l1_square_le {d n D : ℕ} (i : Fin n) {lam : ℝ}
    (hlam : 0 ≤ lam) (L : ℝ) {T : ℝ} (hT : 1 ≤ T)
    (U : Fin n → Covariate d) (hU : ∀ l r, |U l r| ≤ 2) :
    (spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i lam L T U)) ^ 2 ≤
      (100 * (d : ℝ)) ^ (2 * Fintype.card (SpatialScaleIndex i)) *
        ∫ t : SpatialScaleVector i in spatialScaleDomain i T \ spatialScaleDomain i L,
          spatialCardinalScale lam (spatialScaleExtend i t) U i := by
  let s := spatialScaleDomain i T \ spatialScaleDomain i L
  let C : ℝ := (100 * (d : ℝ)) ^ (2 * Fintype.card (SpatialScaleIndex i))
  have hs : s ⊆ Ici 0 := fun _ ht => ht.1.1
  have hμ : volume.restrict s ≤ spatialScaleMeasure i T := Measure.restrict_mono_set volume Set.sdiff_subset
  have hh : Integrable (fun t => spatialMatrixL1 (spatialCenteredCardinalMatrix (D := D) i lam U t))
      (volume.restrict s) :=
    (integrable_finsetSum _ fun β _ => integrable_finsetSum _ fun β' _ =>
      (spatial_centered_cardinal_matrix_integrable i lam T hT U β β').abs).mono_measure hμ
  have hw : Integrable (fun t => spatialCardinalWeight lam (spatialScaleExtend i t) U i) (volume.restrict s) :=
    (spatial_cardinal_weight_orthant_integrable i lam hlam U).mono_measure (Measure.restrict_mono_set volume hs)
  have hscale : Integrable (fun t => spatialCardinalScale lam (spatialScaleExtend i t) U i) (volume.restrict s) :=
    ((spatial_centered_cardinal_scale_continuous i lam U).continuousOn.integrableOn_compact
      (spatial_scale_domain_isCompact i T hT)).mono_set Set.sdiff_subset
  have hnn : ∀ᵐ t ∂volume.restrict s, 0 ≤ spatialCardinalScale lam (spatialScaleExtend i t) U i := by
    filter_upwards [ae_restrict_mem ((spatial_scale_domain_isClosed i T).measurableSet.diff
      (spatial_scale_domain_isClosed i L).measurableSet)] with t ht
    exact spatial_cardinal_scale_nonnegative i lam U t ht.1.1
  have hwn : ∀ᵐ t ∂volume.restrict s, 0 ≤ spatialCardinalWeight lam (spatialScaleExtend i t) U i :=
    (spatial_cardinal_weight_orthant_nonnegative i lam U).filter_mono (ae_mono (Measure.restrict_mono_set volume hs))
  have hdom : ∀ᵐ t ∂volume.restrict s,
      (spatialMatrixL1 (spatialCenteredCardinalMatrix (D := D) i lam U t)) ^ 2 ≤
        spatialCardinalWeight lam (spatialScaleExtend i t) U i *
          (C * spatialCardinalScale lam (spatialScaleExtend i t) U i) := by
    filter_upwards [ae_restrict_mem ((spatial_scale_domain_isClosed i T).measurableSet.diff
      (spatial_scale_domain_isClosed i L).measurableSet)] with t ht
    exact spatial_centered_matrix_l1_square_le_weight_scale i lam U hU t ht.1.1
  have hcs := integral_square_le_weight_mass_mul (volume.restrict s) _ _ _ hh hw (hscale.const_mul C)
    hwn (hnn.mono fun _ ht => mul_nonneg (by dsimp [C]; positivity) ht) hdom
  have hmass : (∫ t in s, spatialCardinalWeight lam (spatialScaleExtend i t) U i) ≤ 1 :=
    (integral_mono_measure (Measure.restrict_mono_set volume hs)
      (spatial_cardinal_weight_orthant_nonnegative i lam U)
      (spatial_cardinal_weight_orthant_integrable i lam hlam U)).trans
        (spatial_cardinal_weight_orthant_integral_le_one i lam hlam U)
  have hnonneg : 0 ≤ ∫ t in s, C * spatialCardinalScale lam (spatialScaleExtend i t) U i :=
    integral_nonneg_of_ae (hnn.mono fun _ ht => mul_nonneg (by dsimp [C]; positivity) ht)
  have hbound := hcs.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hmass hnonneg)
  have htri : spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i lam L T U) ≤
      ∫ t in s, spatialMatrixL1 (spatialCenteredCardinalMatrix (D := D) i lam U t) := by
    have hi (β β' : HighFrameIndex d D) :=
      (spatial_centered_cardinal_matrix_integrable i lam T hT U β β').mono_measure hμ
    unfold spatialMatrixL1 centeredCardinalBandMatrix
    rw [integral_finsetSum _ fun β _ => integrable_finsetSum _ fun β' _ => (hi β β').abs]
    refine Finset.sum_le_sum fun β _ => ?_
    rw [integral_finsetSum _ fun β' _ => (hi β β').abs]
    exact Finset.sum_le_sum fun β' _ => by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        fun t => spatialCenteredCardinalMatrix i lam U t β β'
  exact ((sq_le_sq₀ (spatial_matrix_l1_nonnegative _)
    (integral_nonneg fun _ => spatial_matrix_l1_nonnegative _)).mpr htri).trans
    (by simpa only [integral_const_mul] using hbound)

lemma anchored_patch_configuration_in_box_ae {d n : ℕ} (i : Fin n) (x : Covariate d)
    (hx : x ∈ spatialPatchBox d) :
    ∀ᵐ Y ∂spatialPatchDesignMeasure i d, ∀ l r, |anchoredPatchConfiguration i x Y l r| ≤ 2 := by
  have hae : ∀ᵐ Y ∂spatialPatchDesignMeasure i d, ∀ j : SpatialScaleIndex i, Y j ∈ spatialPatchBox d :=
    ae_all_iff.mpr fun j => (Measure.tendsto_eval_ae_ae
      (μ := fun _ : SpatialScaleIndex i => volume.restrict (spatialPatchBox d)) (i := j)).eventually
        (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hae] with Y hY l r
  by_cases hl : l ≠ i
  · have hh := hY ⟨l, hl⟩
    simp only [anchoredPatchConfiguration, dite_eq_left hl]
    exact (abs_le.mpr ⟨hh.1 r, hh.2 r⟩).trans (by norm_num)
  · obtain rfl := not_ne_iff.mp hl
    rw [anchored_configuration_same]
    exact (abs_le.mpr ⟨hx.1 r, hx.2 r⟩).trans (by norm_num)

theorem anchored_centered_band_matrix_l1_square_integrable {d n D : ℕ} (i : Fin n)
    {lam T : ℝ} (hlam : 0 ≤ lam) (hT : 1 ≤ T) (L : ℝ) (x : Covariate d) (hx : x ∈ spatialPatchBox d) :
    Integrable (fun Y => (spatialMatrixL1 (anchoredCenteredCardinalBandMatrix (D := D) i lam L T x Y)) ^ 2)
      (spatialPatchDesignMeasure i d) := by
  have hcfg : Continuous (anchoredPatchConfiguration i x) :=
    continuous_pi fun l => by unfold anchoredPatchConfiguration; split_ifs <;> fun_prop
  have hm : Measurable fun Y => (spatialMatrixL1 (anchoredCenteredCardinalBandMatrix (D := D) i lam L T x Y)) ^ 2 := by
    unfold spatialMatrixL1
    refine (Finset.measurable_fun_sum _ fun β _ => Finset.measurable_fun_sum _ fun β' _ => ?_).pow_const 2
    have hc (γ : HighFrameIndex d D) :
        Continuous fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
          highFrameCoefficients (spatialCardinalPolynomial (anchoredPatchConfiguration i x z.2) i) γ :=
      (spatial_cardinal_polynomial_coefficients_continuous i (polynomialBoxExponent γ.val)).comp
        (hcfg.comp continuous_snd)
    exact ((((anchored_cardinal_scale_continuous_actual i lam x).mul (hc β)).mul (hc β')).stronglyMeasurable.integral_prod_left'
      (μ := volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L))).measurable.abs
  refine ((anchored_cardinal_band_scale_joint_integrable i hlam hT L x).integral_prod_right.const_mul
    ((100 * (d : ℝ)) ^ (2 * Fintype.card (SpatialScaleIndex i)))).mono' hm.aestronglyMeasurable ?_
  filter_upwards [anchored_patch_configuration_in_box_ae i x hx] with Y hY
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact centered_cardinal_band_matrix_l1_square_le i hlam L hT (anchoredPatchConfiguration i x Y) hY

theorem anchored_centered_band_matrix_l1_square_integral_le {d n D : ℕ} (hd : 5 ≤ d) (hn : 2 ≤ n)
    (i : Fin n) (x : Covariate d) (hx : x ∈ spatialPatchBox d) {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) :
    (∫ Y, (spatialMatrixL1 (anchoredCenteredCardinalBandMatrix (D := D) i (spatialInterpolationLambda d) L T x Y)) ^ 2
      ∂spatialPatchDesignMeasure i d) ≤
      ((100 * (d : ℝ)) ^ 2 * 16 * spatialScaleIntegralConstant d) ^ (n - 1) *
        L ^ (4 - (d : ℝ)) * (1 + Real.log L) ^ (n - 2) := by
  have hd0 : 0 < d := by omega
  have hdR : (5 : ℝ) ≤ d := by exact_mod_cast hd
  let b : ℝ := ((d : ℝ) - 4) / 2
  have hb : (1 / 2 : ℝ) ≤ b := by dsimp [b]; linarith
  have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  have hjoint := anchored_cardinal_band_scale_joint_integrable i hlam hT L x
  have hi := hjoint.integral_prod_right.const_mul ((100 * (d : ℝ)) ^ (2 * Fintype.card (SpatialScaleIndex i)))
  have hfirst := integral_mono_ae (anchored_centered_band_matrix_l1_square_integrable (D := D) i hlam hT L x hx) hi <| by
    filter_upwards [anchored_patch_configuration_in_box_ae i x hx] with Y hY
    exact centered_cardinal_band_matrix_l1_square_le (D := D) i hlam L hT (anchoredPatchConfiguration i x Y) hY
  rw [integral_const_mul, spatial_scale_index_card] at hfirst
  have hband : (∫ Y, (∫ t in spatialScaleDomain i T \ spatialScaleDomain i L,
      anchoredCardinalScale i (spatialInterpolationLambda d) x t Y) ∂spatialPatchDesignMeasure i d) ≤
      (16 * spatialScaleIntegralConstant d) ^ (n - 1) * L ^ (4 - (d : ℝ)) * (1 + Real.log L) ^ (n - 2) := by
    rw [(integral_prod_symm _ hjoint).symm.trans (integral_prod _ hjoint)]
    have hsub : spatialScaleDomain i T \ spatialScaleDomain i L ⊆ Ici 0 \ spatialScaleDomain i L :=
      fun _ ht => ⟨ht.1.1, ht.2⟩
    have hμ := Measure.restrict_mono_set (volume : Measure (SpatialScaleVector i)) hsub
    have hpowint : Integrable (fun t : SpatialScaleVector i => ∏ j, (1 + t j) ^ (-b - 1 : ℝ))
        (volume.restrict (Ici 0 \ spatialScaleDomain i L)) :=
      spatial_scale_complement_power_integrable hn i (by linarith : 0 < b) L
    have hdom : (fun t : SpatialScaleVector i =>
        ∫ Y, anchoredCardinalScale i (spatialInterpolationLambda d) x t Y ∂spatialPatchDesignMeasure i d) ≤ᵐ[
          volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L)]
        fun t => (spatialScaleIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i) *
          ∏ j, (1 + t j) ^ (-b - 1 : ℝ) := by
      filter_upwards [ae_restrict_mem ((spatial_scale_domain_isClosed i T).measurableSet.diff
        (spatial_scale_domain_isClosed i L).measurableSet)] with t ht
      simp_rw [anchored_cardinal_scale_product_actual]
      unfold spatialPatchDesignMeasure
      rw [integral_fintype_prod_eq_prod fun (j : SpatialScaleIndex i) (y : Covariate d) =>
        t j * (spatialInterpolationLambda d) ^ 2 *
          Real.exp (-(t j * spatialInterpolationLambda d * spatialSquaredDistance x y))]
      have hp : (∏ j : SpatialScaleIndex i, ∫ y in spatialPatchBox d,
          t j * (spatialInterpolationLambda d) ^ 2 *
            Real.exp (-(t j * spatialInterpolationLambda d * spatialSquaredDistance x y))) ≤
          ∏ j : SpatialScaleIndex i, spatialScaleIntegralConstant d * (1 + t j) ^ (1 - (d : ℝ) / 2) := by
        refine Finset.prod_le_prod₀ (fun j _ => integral_nonneg fun _ =>
          mul_nonneg (mul_nonneg (ht.1.1 j) (sq_nonneg _)) (Real.exp_pos _).le) fun j _ => ?_
        rw [show (fun y : Covariate d => t j * (spatialInterpolationLambda d) ^ 2 *
            Real.exp (-(t j * spatialInterpolationLambda d * spatialSquaredDistance x y))) =
          fun y => (spatialInterpolationLambda d) ^ 2 *
            (t j * Real.exp (-(t j * spatialInterpolationLambda d * spatialSquaredDistance x y))) from
          funext fun _ => by ring, integral_const_mul]
        simpa only [spatialScaleIntegralConstant, mul_assoc] using
          mul_le_mul_of_nonneg_left (spatial_scale_exponential_patch_integral_decay hd0 (t j) (ht.1.1 j) x hx)
            (sq_nonneg (spatialInterpolationLambda d))
      simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        show 1 - (d : ℝ) / 2 = -b - 1 by dsimp [b]; ring] using hp
    have hnn : ∀ᵐ t ∂volume.restrict (Ici 0 \ spatialScaleDomain i L),
        0 ≤ ∏ j : SpatialScaleIndex i, (1 + t j) ^ (-b - 1 : ℝ) := by
      filter_upwards [ae_restrict_mem (measurableSet_Ici.diff (spatial_scale_domain_isClosed i L).measurableSet)] with t ht
      exact Finset.prod_nonneg fun j _ => Real.rpow_nonneg (by have : (0 : ℝ) ≤ t j := ht.1 j; linarith) _
    have hC : 0 ≤ (spatialScaleIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i) := by
      unfold spatialScaleIntegralConstant; positivity
    have hf1 := integral_mono_ae hjoint.integral_prod_left ((hpowint.mono_measure hμ).const_mul _) hdom
    rw [integral_const_mul] at hf1
    have hfull := hf1.trans ((mul_le_mul_of_nonneg_left (integral_mono_measure hμ hnn hpowint) hC).trans
      (mul_le_mul_of_nonneg_left (spatial_scale_complement_power_integral_le hn i hb hL) hC))
    rw [spatial_scale_index_card, show -2 * b = 4 - (d : ℝ) by dsimp [b]; ring] at hfull
    simpa only [mul_pow, mul_assoc, mul_comm, mul_left_comm] using hfull
  have hfull := hfirst.trans (mul_le_mul_of_nonneg_left hband (by positivity : 0 ≤ (100 * (d : ℝ)) ^ (2 * (n - 1))))
  rw [show 2 * (n - 1) = (n - 1) * 2 by omega, pow_mul] at hfull
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm, mul_assoc, mul_comm, mul_left_comm] using hfull

theorem spatial_centered_cardinal_matrix_joint_continuous {d n D : ℕ} (i : Fin n) (lam : ℝ)
    (β β' : HighFrameIndex d D) :
    Continuous fun z : (Fin n → Covariate d) × SpatialScaleVector i =>
      spatialCenteredCardinalMatrix i lam z.1 z.2 β β' := by
  have hsc : Continuous fun z : (Fin n → Covariate d) × SpatialScaleVector i =>
      spatialCardinalScale lam (spatialScaleExtend i z.2) z.1 i := by
    simp_rw [spatial_cardinal_scale_product]; unfold spatialSquaredDistance; fun_prop
  have hc (γ : HighFrameIndex d D) : Continuous fun z : (Fin n → Covariate d) × SpatialScaleVector i =>
      highFrameCoefficients (spatialCardinalPolynomial z.1 i) γ :=
    (spatial_cardinal_polynomial_coefficients_continuous i (polynomialBoxExponent γ.val)).comp continuous_fst
  exact (hsc.mul (hc β)).mul (hc β')

theorem integrated_cardinal_weight_continuous {d n : ℕ} (i : Fin n) (lam : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    Continuous fun U : Fin n → Covariate d => integratedCardinalWeight lam T U i := by
  unfold integratedCardinalWeight spatialScaleMeasure
  refine continuous_parametric_integral_of_continuous ?_ (spatial_scale_domain_isCompact i T hT)
  simp_rw [spatial_cardinal_weight_scale_product]
  unfold spatialUnaryWeight spatialSquaredDistance; fun_prop

theorem integrated_cardinal_band_continuous {d n D : ℕ} (lam : ℝ) {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T)
    (β β' : HighFrameIndex d D) :
    Continuous fun U : Fin n → Covariate d =>
      integratedCardinalMatrix lam T U β β' - integratedCardinalMatrix lam L U β β' := by
  have hmat {S : ℝ} (hS : 1 ≤ S) : Continuous fun U : Fin n → Covariate d => integratedCardinalMatrix lam S U β β' := by
    unfold integratedCardinalMatrix spatialScaleMeasure
    exact continuous_finsetSum _ fun i _ => continuous_parametric_integral_of_continuous
      (spatial_centered_cardinal_matrix_joint_continuous i lam β β') (spatial_scale_domain_isCompact i S hS)
  exact (hmat hT).sub (hmat hL)

end CardinalBandCluster

-- ============================================================================
-- 2. Frame Evaluation, Score Orthogonality/Bounds, and Fine-Pair Packets
-- ============================================================================

section FrameOrthogonalityAndPackets
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def highFrameMonomial {d D : ℕ} (γ : HighFrameIndex d D) : MvPolynomial (Fin d) ℝ :=
  MvPolynomial.monomial (polynomialBoxExponent γ.val) 1

section FrameEval
attribute [local instance] Classical.propDecidable

theorem highPeriodizedFrame_evaluation (d k D : ℕ) (j : HighWindowLabels d k)
    (c : HighFrameIndex d D → ℝ) (x : Covariate d) :
    highPeriodizedChart d k j (highFrameProfile (highFramePolynomial c)) x =
      ∑ γ, c γ * highPeriodizedChart d k j (highFrameProfile (highFrameMonomial γ)) x := by
  have hprof (u : Covariate d) : highFrameProfile (highFramePolynomial c) u =
      ∑ γ, c γ * highFrameProfile (highFrameMonomial γ) u := by
    unfold highFrameProfile
    rw [highFramePolynomial_scaled_eval, Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [frameScaledPolynomial_eval]
    unfold highFrameMonomial highFrameFeature
    rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_fintype _ _ fun _ => pow_zero _]
    simp only [polynomial_box_exponent_apply]; ring
  have hfinite (γ : HighFrameIndex d D) : HasFiniteSupport fun z : Fin d → ℤ =>
      c γ * (if ∀ r, (z r : ZMod k) = j r then
        highFrameProfile (highFrameMonomial γ) (fun r => (k : ℝ) * x r - z r) else 0) :=
    HasFiniteSupport.mul_right (fun _ => c γ)
      ((highPeriodizedChart_locallyFinite d k j _
        (highFrameProfile_zero_of_window_zero (highFrameMonomial γ))).point_finite x)
  unfold highPeriodizedChart
  calc
    _ = ∑ᶠ z : Fin d → ℤ, ∑ γ : HighFrameIndex d D,
        c γ * (if ∀ r, (z r : ZMod k) = j r then
          highFrameProfile (highFrameMonomial γ) (fun r => (k : ℝ) * x r - z r) else 0) :=
      finsum_congr fun z => by
        by_cases hz : ∀ r, (z r : ZMod k) = j r
        · simp only [ite_eq_left hz]; exact hprof _
        · simp only [ite_eq_right hz, mul_zero, Finset.sum_const_zero]
    _ = ∑ γ : HighFrameIndex d D, ∑ᶠ z : Fin d → ℤ,
        c γ * (if ∀ r, (z r : ZMod k) = j r then
          highFrameProfile (highFrameMonomial γ) (fun r => (k : ℝ) * x r - z r) else 0) :=
      (sum_finsum_comm Finset.univ _ fun γ _ => hfinite γ).symm
    _ = _ := by simp_rw [← mul_finsum]

theorem highFrameField_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    (d k D : ℕ) [NeZero k] (η : ℝ)
    (c : Ω → HighWindowLabels d k → HighFrameIndex d D → ℝ) (hc : Measurable c) :
    Measurable fun ωx : Ω × Covariate d =>
      highFrameField d k η (fun j => highFramePolynomial (c ωx.1 j)) ωx.2 := by
  unfold highFrameField
  simp_rw [highPeriodizedFrame_evaluation]
  refine Measurable.const_mul (Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun γ _ => ?_) _
  exact (((measurable_pi_apply γ).comp ((measurable_pi_apply j).comp hc)).comp measurable_fst).mul
    ((highPeriodizedChart_contDiff d k j _ (highFrameProfile_contDiff (highFrameMonomial γ))
      (highFrameProfile_zero_of_window_zero (highFrameMonomial γ))).continuous.measurable.comp measurable_snd)

theorem high_response_ratio_depends_on_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (a V η : ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c v : ι → ℝ)
    (S : Finset (Fin n)) (hw : ∀ i, i ∉ S → w i = 0)
    (y y' : Fin n → Fin 3) (hyy : ∀ i ∈ S, y i = y' i)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b) :
    highResponseProduct a V η g w φ v y / highResponseProduct a V η g w φ c y =
      highResponseProduct a V η g w φ v y' / highResponseProduct a V η g w φ c y' := by
  let outside (z : Fin n → Fin 3) : ℝ :=
    ∏ i ∈ (Finset.univ : Finset (Fin n)) \ S, ternaryMass a (g i) V (z i)
  let inside (z : Fin n → Fin 3) (u : ι → ℝ) : ℝ :=
    ∏ i ∈ S, ternaryMass a (coefficientRegression η g w φ u i) V (z i)
  have hfactor (z : Fin n → Fin 3) (u : ι → ℝ) :
      highResponseProduct a V η g w φ u z = outside z * inside z u := by
    unfold highResponseProduct
    rw [← Finset.prod_sdiff (Finset.subset_univ S)]; dsimp [outside, inside]; congr 1
    exact Finset.prod_congr rfl fun i hi => by simp [coefficientRegression, hw i (Finset.mem_sdiff.mp hi).2]
  have hout (z : Fin n → Fin 3) : outside z ≠ 0 :=
    ne_of_gt (Finset.prod_pos fun i hi => by
      simpa [coefficientRegression, hw i (Finset.mem_sdiff.mp hi).2] using hp i (z i))
  have hin (z : Fin n → Fin 3) : inside z c ≠ 0 := ne_of_gt (Finset.prod_pos fun i _ => hp i (z i))
  have hs (u : ι → ℝ) : inside y u = inside y' u := Finset.prod_congr rfl fun i hi => by rw [hyy i hi]
  rw [hfactor y v, hfactor y c, hfactor y' v, hfactor y' c, hs v, hs c]
  field_simp [hout y, hout y', hin y']

theorem high_response_variance_ratio {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (a V η : ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (y : Fin n → Fin 3) (i : Fin n)
    (hp : ∀ k, 0 < ternaryMass a (coefficientRegression η g w φ c k) V (y k)) :
    highResponseVarianceTerm a V η g w φ c y i / highResponseProduct a V η g w φ c y =
      ternaryVarianceDerivative a (y i) /
        ternaryMass a (coefficientRegression η g w φ c i) V (y i) := by
  unfold highResponseVarianceTerm highResponseProduct
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact mul_div_mul_right _ _ (ne_of_gt (Finset.prod_pos fun k _ => hp k))

theorem local_response_scores_orthogonal {n : ℕ}
    (μ : Fin n → Measure (Fin 3)) [∀ i, IsProbabilityMeasure (μ i)]
    (r s : (Fin n → Fin 3) → ℝ) (S T : Finset (Fin n)) (hST : Disjoint S T)
    (hr : ∀ y y', (∀ i ∈ S, y i = y' i) → r y = r y')
    (hs : ∀ y y', (∀ i ∈ T, y i = y' i) → s y = s y')
    (hc : (∫ y, r y ∂Measure.pi μ) = 0) :
    (∫ y, r y * s y ∂Measure.pi μ) = 0 := by
  let R (y : S → Fin 3) := r (extendPatchResponses n S y)
  let Q (y : T → Fin 3) := s (extendPatchResponses n T y)
  have hR (y : Fin n → Fin 3) : r y = R fun i : S => y i :=
    hr _ _ fun i hi => by simp [extendPatchResponses, hi]
  have hQ (y : Fin n → Fin 3) : s y = Q fun i : T => y i :=
    hs _ _ fun i hi => by simp [extendPatchResponses, hi]
  simp_rw [hR, hQ]
  exact finite_product_local_scores_orthogonal n μ S T hST R Q (by simpa only [← hR] using hc)

def highPatchSampleIndices (d k n : ℕ) (j : HighWindowLabels d k)
    (x : Fin n → Covariate d) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i ∈ highTorusPatch d k j

theorem highPatchSampleIndices_disjoint (d k n : ℕ) [NeZero k]
    (x : Fin n → Covariate d) (j l : HighWindowLabels d k)
    (hjl : l ∉ highNeighborLabels d k j) :
    Disjoint (highPatchSampleIndices d k n j x) (highPatchSampleIndices d k n l x) :=
  Finset.disjoint_left.mpr fun _ hi hj =>
    Set.disjoint_left.mp (highTorusPatch_disjoint_of_not_neighbor d k j l hjl)
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

theorem highPeriodicTensor_sample_zero_outside_patch (d k n : ℕ)
    (j : HighWindowLabels d k) (x : Fin n → Covariate d) (i : Fin n)
    (hi : i ∉ highPatchSampleIndices d k n j x) :
    highPeriodicTensor d k j (x i) = 0 := by
  by_contra h
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, highPeriodicTensor_supported_patch d k j h⟩)

def highSeparatedDerivativeBudget (a ρ : ℝ) : ℝ :=
  4 * (((2 * ρ + a) / a ^ 2) ^ 2 + 2 / a ^ 2)

theorem high_response_variance_correction_abs_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : 1 ≤ n)
    (a V η pPlus : ℝ) (ha : 0 < a) (hpPlus : 0 ≤ pPlus)
    (p g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hw : ∀ i, |w i| ≤ 1) (hIncoming : ∀ i, |p i| ≤ pPlus)
    (hp : ∀ i u, 0 ≤ ternaryMass a (coefficientRegression η g w φ c i) V u)
    (y : Fin n → Fin 3) :
    |η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i| ≤
      pPlus ^ n * (1 / a ^ 2) * (n : ℝ) ^ 2 * η ^ 2 := by
  have hvar : |∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i| ≤ (n : ℝ) / a ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => ?_ : _ ≤ ∑ _i : Fin n, 1 / a ^ 2).trans_eq (by simp [div_eq_mul_inv]))
    rw [abs_mul, abs_of_nonneg (sq_nonneg (w i))]
    have hwsq : (w i) ^ 2 ≤ 1 := by simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hw i) 2
    exact (mul_le_mul hwsq (high_response_variance_term_abs_bound a V η ha g w φ c hp y i)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg η)]
  calc
    _ ≤ η ^ 2 * pPlus ^ n * ((n : ℝ) / a ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (finite_density_product_abs_bound p pPlus hpPlus hIncoming) (sq_nonneg η))
        hvar (abs_nonneg _) (by positivity)
    _ ≤ η ^ 2 * pPlus ^ n * ((n : ℝ) ^ 2 / a ^ 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by nlinarith only [hn1]) (sq_nonneg a)) (by positivity)
    _ = _ := by ring

def highSeparatedScoreExponentialConstant (a ρ pPlus pMinus cMass : ℝ) : ℝ :=
  4 * max 1 (pPlus / (pMinus * cMass)) *
    max 1 (highSeparatedDerivativeBudget a ρ + 1 / a ^ 2)

theorem highSeparatedScoreExponentialConstant_pos (a ρ pPlus pMinus cMass : ℝ) :
    0 < highSeparatedScoreExponentialConstant a ρ pPlus pMinus cMass :=
  mul_pos (mul_pos (by norm_num) (lt_of_lt_of_le one_pos (le_max_left _ _)))
    (lt_of_lt_of_le one_pos (le_max_left _ _))

theorem highSeparated_score_budget_absorb (n : ℕ) (hn : 1 ≤ n)
    (a ρ pPlus pMinus cMass η B : ℝ) (hpPlus : 0 ≤ pPlus)
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass) (hB : 0 ≤ B) :
    (pPlus / (pMinus * cMass)) ^ n *
      (highSeparatedDerivativeBudget a ρ * B + 1 / a ^ 2) * (n : ℝ) ^ 2 * η ^ 2 ≤
      (highSeparatedScoreExponentialConstant a ρ pPlus pMinus cMass) ^ n *
        η ^ 2 * (B + 1) := by
  let R : ℝ := max 1 (pPlus / (pMinus * cMass))
  let K : ℝ := max 1 (highSeparatedDerivativeBudget a ρ + 1 / a ^ 2)
  have hK1 : 1 ≤ K := le_max_left _ _
  have hder : 0 ≤ highSeparatedDerivativeBudget a ρ := by unfold highSeparatedDerivativeBudget; positivity
  have hK : highSeparatedDerivativeBudget a ρ * B + 1 / a ^ 2 ≤ K * (B + 1) := by
    have hk : highSeparatedDerivativeBudget a ρ + 1 / a ^ 2 ≤ K := le_max_right _ _
    have hz : 0 ≤ 1 / a ^ 2 := by positivity
    nlinarith only [hk, hB, hder, hz, mul_nonneg hB hz]
  have hnReal : (2 : ℝ) * (n : ℝ) ^ 2 + 1 ≤ 2 ^ (2 * n) := by exact_mod_cast Nat.two_mul_sq_add_one_le_two_pow_two_mul n
  have hnsq : (n : ℝ) ^ 2 ≤ (4 : ℝ) ^ n := by
    rw [show (2 : ℝ) ^ (2 * n) = (4 : ℝ) ^ n by rw [pow_mul]; norm_num] at hnReal
    nlinarith only [hnReal, sq_nonneg (n : ℝ)]
  have hRpow : (pPlus / (pMinus * cMass)) ^ n ≤ R ^ n :=
    pow_le_pow_left₀ (div_nonneg hpPlus (mul_pos hpMinus hcMass).le) (le_max_right _ _) _
  have hKpow : K ≤ K ^ n := le_self_pow₀ hK1 (by omega)
  calc
    _ ≤ (R ^ n * (K * (B + 1))) * (4 : ℝ) ^ n * η ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul hRpow hK (by positivity) (by positivity)) hnsq
          (sq_nonneg _) (by positivity)) (sq_nonneg η)
    _ ≤ (R ^ n * (K ^ n * (B + 1))) * (4 : ℝ) ^ n * η ^ 2 := by gcongr
    _ = _ := by dsimp [highSeparatedScoreExponentialConstant, R, K]; simp only [mul_pow]; ring

def highCardinalDensityReset {d n : ℕ} (ad bd lam : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (ζ : CardinalSeparatedMark d n) (z : ℝ) (ε : Fin n → ℝ) (i : Fin n) : ℝ :=
  localDensityReset ad bd n z ε p (fun i l => cardinalSeparatedFactor lam ζ l (U i)) i

theorem high_cardinal_packet_action_exact {d n F : ℕ}
    (ad bd lam : ℝ) (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    {T : ℝ} (hT : 1 ≤ T) (m D q : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hnD : n ≤ D)
    (C : ℝ) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    highSeparatedPacketAction (cardinalSeparatedMeasure d n T) ad bd m n D q C
      (cardinalSeparatedAmplitude lam) c
      (fun ζ z ε => ∏ i, highCardinalDensityReset ad bd lam U p ζ z ε i) Φ =
        (∏ i, p i) * responseMatrixAction q C (integratedCardinalMatrix lam T U) c Φ := by
  have h := highSeparatedPacketAction_count_selector (cardinalSeparatedMeasure d n T) ad bd ha hab
    m n D q hn (hn.trans hnD) (Finset.univ : Finset (Fin n)) (by simpa using hnD)
    (by simpa using hnm) (by simp) p
    (fun ζ i l => cardinalSeparatedFactor lam ζ l (U i))
    (fun i l => cardinal_separated_factor_measurable lam l (U i))
    (fun ζ i l => cardinal_separated_factor_abs_le_one lam ζ l (U i) (hU i)) C
    (cardinalSeparatedAmplitude lam) (cardinal_separated_amplitude_measurable lam)
    (cardinal_separated_cost_integrable lam hT) c Φ
  simp only [highCardinalDensityReset]
  rw [h]
  have hpow : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  have huniv : separatedSubsetMatrix (cardinalSeparatedMeasure d n T) n
      (fun ζ i l => cardinalSeparatedFactor lam ζ l (U i))
      (cardinalSeparatedAmplitude (D := F) lam) Finset.univ =
        integratedCardinalMatrix lam T U := by
    funext β β'; unfold separatedSubsetMatrix
    simp_rw [cardinal_density_separated_sym_eq]
    exact (integrated_cardinal_symmetric_separated_exact lam hlam hT U hU β β').symm
  simp only [Finset.card_univ, Fintype.card_fin, ite_true, hpow, Finset.sum_singleton, huniv]

end FrameEval

def fineModulationNode (i : Fin 3) : ℝ := if i = 0 then -1 else if i = 1 then 0 else 1
def fineModulationWeight (i : Fin 3) : ℝ := if i = 1 then -1 else 1 / 2

lemma fineModulation_eval (f : ℝ → ℝ) :
    (∑ i : Fin 3, fineModulationWeight i * f (fineModulationNode i)) =
      f (-1) / 2 - f 0 + f 1 / 2 := by
  simp [Fin.sum_univ_succ, fineModulationWeight, fineModulationNode]; ring

theorem fineModulationNode_bound (i : Fin 3) : |fineModulationNode i| ≤ 1 := by
  fin_cases i <;> norm_num [fineModulationNode]

lemma fineModulation_moment (n : ℕ) :
    (∑ i : Fin 3, fineModulationWeight i * fineModulationNode i ^ n) =
      if n = 0 then 0 else if Even n then 1 else 0 := by
  rw [fineModulation_eval fun z => z ^ n]
  by_cases hn0 : n = 0
  · subst n; norm_num
  · rw [ite_eq_right hn0, zero_pow hn0]
    rcases Nat.even_or_odd n with hn | hn
    · rw [ite_eq_left hn, hn.neg_one_pow]; norm_num
    · rw [ite_eq_right (Nat.not_even_iff_odd.mpr hn), hn.neg_one_pow]; norm_num

abbrev FinePairDensityIndex (M : ℕ) := Fin (M + 3) × Fin 3
def finePairDensityPrefactor (a b : ℝ) : ℝ := b ^ 2 / densityMargin a b 0 ^ 2
def finePairDensityAtom (a b : ℝ) (M : ℕ) (i : FinePairDensityIndex M) : ℝ × ℝ :=
  (exteriorNode a b (M + 2) i.1, fineModulationNode i.2)
def finePairDensityWeight (a b : ℝ) (M : ℕ) (i : FinePairDensityIndex M) : ℝ :=
  finePairDensityPrefactor a b * exteriorWeight a b (M + 2) i.1 * fineModulationWeight i.2
def finePairDensitySignedRule (a b : ℝ) (M : ℕ) : SignedMeasure (ℝ × ℝ) :=
  atomicSignedRule (finePairDensityAtom a b M) (finePairDensityWeight a b M)

theorem finePairDensityWeight_variation (a b : ℝ) (ha : 0 < a) (hab : a < b) (M : ℕ) :
    (∑ i : FinePairDensityIndex M, |finePairDensityWeight a b M i|) =
      2 * |finePairDensityPrefactor a b| *
        Real.cosh ((M + 2 : ℕ) * exteriorTau ((a + b) / (b - a))) := by
  simp only [finePairDensityWeight, abs_mul, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, show (∑ i : Fin 3, |fineModulationWeight i|) = 2 by
    norm_num [Fin.sum_univ_succ, fineModulationWeight]]
  rw [← Finset.sum_mul, ← Finset.mul_sum, exterior_rule_variation a b ha hab (M + 2) (by omega)]; ring

def finePairDensityReset {U : Type*} (a b : ℝ) (z eps : ℝ) (p ψ : U → ℝ) (u : U) : ℝ :=
  z + densityMargin a b z / b * p u * eps * ψ u

theorem finePairDensityReset_mem_interval {U : Type*} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (z eps : ℝ) (hz : z ∈ Icc a b) (heps : |eps| ≤ 1)
    (p ψ : U → ℝ) (u : U) (hp : p u ∈ Icc a b) (hψ : |ψ u| ≤ 1) :
    finePairDensityReset a b z eps p ψ u ∈ Icc a b := by
  simpa [localDensityReset, finePairDensityReset, mul_comm, mul_left_comm, mul_assoc] using
    localDensityReset_mem_interval a b ha hab 1 (by omega) z hz (fun _ => eps)
      (fun _ => heps) p (fun u _ => ψ u) u hp fun _ => hψ

def finePairCountCoefficient (a b : ℝ) (M k j : ℕ) : ℝ :=
  finePairDensityPrefactor a b * ∑ h : Fin (M + 3), exteriorWeight a b (M + 2) h *
    (exteriorNode a b (M + 2) h ^ (k - j) * (densityMargin a b (exteriorNode a b (M + 2) h) / b) ^ j)

theorem finePairCountCoefficient_two_exact (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (M k : ℕ) (hk : 2 ≤ k) (hM : k ≤ M) :
    finePairCountCoefficient a b M k 2 = if k = 2 then 1 else 0 := by
  rw [show finePairCountCoefficient a b M k 2 = densityCountCoefficient a b M 2 k by
    unfold finePairCountCoefficient finePairDensityPrefactor densityCountCoefficient
    rw [Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun _ _ => by field_simp [densityMargin_zero_ne a b ha hab, (ha.trans hab).ne']]
  exact densityCountCoefficient_exact a b ha hab M 2 k (by omega) hk hM

theorem finePairCountCoefficient_abs_bound (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (M k j : ℕ) :
    |finePairCountCoefficient a b M k j| ≤
      |finePairDensityPrefactor a b| * (b ^ (k - j) * ((b - a) / (4 * b)) ^ j) *
        Real.cosh ((M + 2 : ℕ) * exteriorTau ((a + b) / (b - a))) := by
  have hb : 0 < b := ha.trans hab
  have hterm (h : Fin (M + 3)) :
      |exteriorNode a b (M + 2) h ^ (k - j) * (densityMargin a b (exteriorNode a b (M + 2) h) / b) ^ j| ≤
      b ^ (k - j) * ((b - a) / (4 * b)) ^ j := by
    have hz := exteriorNode_mem a b hab.le (M + 2) h
    have ht := densityMargin_bounds a b hab _ hz
    have ht0 : 0 ≤ densityMargin a b (exteriorNode a b (M + 2) h) / b := div_nonneg ht.1 hb.le
    rw [abs_mul, abs_pow, abs_pow, abs_of_nonneg (ha.le.trans hz.1), abs_of_nonneg ht0]
    exact mul_le_mul (pow_le_pow_left₀ (ha.le.trans hz.1) hz.2 _)
      (pow_le_pow_left₀ ht0 ((div_le_div_of_nonneg_right ht.2.2.2 hb.le).trans_eq (by ring)) _)
      (pow_nonneg ht0 _) (pow_nonneg hb.le _)
  unfold finePairCountCoefficient; rw [abs_mul]
  refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)).trans ?_
  calc
    _ ≤ |finePairDensityPrefactor a b| *
        ∑ h : Fin (M + 3), |exteriorWeight a b (M + 2) h| * (b ^ (k - j) * ((b - a) / (4 * b)) ^ j) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hterm h) (abs_nonneg _)) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, exterior_rule_variation a b ha hab (M + 2) (by omega)]; ring

theorem finePairDensityWeight_exponential_cost (a b : ℝ) (ha : 0 < a) (hab : a < b) (M : ℕ) :
    (∑ h : FinePairDensityIndex M, |finePairDensityWeight a b M h|) ≤
      (2 * |finePairDensityPrefactor a b| * Real.exp (2 * exteriorTau ((a + b) / (b - a)))) *
        Real.exp ((M : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  rw [finePairDensityWeight_variation a b ha hab M]
  have he : Real.cosh ((M + 2 : ℕ) * exteriorTau ((a + b) / (b - a))) ≤
      Real.exp ((M + 2 : ℕ) * exteriorTau ((a + b) / (b - a))) := by
    rw [← exterior_rule_variation a b ha hab (M + 2) (by omega)]
    exact exterior_rule_variation_le_exp a b ha hab (M + 2) (by omega)
  refine (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq ?_
  rw [Nat.cast_add, Nat.cast_ofNat, add_mul, Real.exp_add]; ring

lemma finePairDensitySignedRule_integral (a b : ℝ) (M : ℕ) (f : ℝ → ℝ → ℝ) :
    (∫ᵛ e, f e.1 e.2 ∂<•finePairDensitySignedRule a b M) =
      finePairDensityPrefactor a b * ∑ j : Fin (M + 3), exteriorWeight a b (M + 2) j *
        ∑ i : Fin 3, fineModulationWeight i * f (exteriorNode a b (M + 2) j) (fineModulationNode i) := by
  rw [finePairDensitySignedRule, atomicSignedRule_integral]
  simp only [finePairDensityAtom, finePairDensityWeight, Fintype.sum_prod_type]
  simp_rw [mul_assoc, ← Finset.mul_sum]

theorem finePairDensitySignedRule_product_expansion {U : Type*} [DecidableEq U]
    (a b : ℝ) (M : ℕ) (S : Finset U) (p ψ : U → ℝ) :
    (∫ᵛ e, ∏ u ∈ S, finePairDensityReset a b e.1 e.2 p ψ u
      ∂<•finePairDensitySignedRule a b M) =
      ∑ W ∈ S.powerset, finePairCountCoefficient a b M S.card W.card * (∏ u ∈ W, p u * ψ u) *
        (if W.card = 0 then 0 else if Even W.card then 1 else 0) := by
  have hmod (z : ℝ) (c : U → ℝ) :
      (∑ h : Fin 3, fineModulationWeight h * ∏ i ∈ S, (z + c i * fineModulationNode h)) =
        ∑ W ∈ S.powerset, z ^ (S.card - W.card) * (∏ i ∈ W, c i) *
          (if W.card = 0 then 0 else if Even W.card then 1 else 0) := by
    simp_rw [add_comm z, Finset.prod_add, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun W hW => ?_
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hW)]
    simp_rw [show ∀ h : Fin 3, fineModulationWeight h *
        ((∏ i ∈ W, c i) * fineModulationNode h ^ W.card * z ^ (S.card - W.card)) =
      z ^ (S.card - W.card) * (∏ i ∈ W, c i) * (fineModulationWeight h * fineModulationNode h ^ W.card)
      from fun _ => by ring]
    rw [← Finset.mul_sum, fineModulation_moment]
  rw [finePairDensitySignedRule_integral a b M fun z eps => ∏ u ∈ S, finePairDensityReset a b z eps p ψ u]
  have hprod (z : ℝ) (W : Finset U) :
      (∏ u ∈ W, densityMargin a b z / b * (p u * ψ u)) =
        (densityMargin a b z / b) ^ W.card * ∏ u ∈ W, p u * ψ u := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp_rw [show ∀ (z eps : ℝ) (u : U), finePairDensityReset a b z eps p ψ u =
    z + (densityMargin a b z / b * (p u * ψ u)) * eps from fun _ _ _ => by unfold finePairDensityReset; ring,
    hmod, hprod]
  rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun W _ => ?_
  unfold finePairCountCoefficient
  simp_rw [show ∀ h : Fin (M + 3), finePairDensityPrefactor a b *
      (exteriorWeight a b (M + 2) h *
       (exteriorNode a b (M + 2) h ^ (S.card - W.card) *
        ((densityMargin a b (exteriorNode a b (M + 2) h) / b) ^ W.card * ∏ u ∈ W, p u * ψ u) *
        (if W.card = 0 then 0 else if Even W.card then 1 else 0))) =
      finePairDensityPrefactor a b *
        (exteriorWeight a b (M + 2) h * (exteriorNode a b (M + 2) h ^ (S.card - W.card) *
          (densityMargin a b (exteriorNode a b (M + 2) h) / b) ^ W.card)) *
        ((∏ u ∈ W, p u * ψ u) * (if W.card = 0 then 0 else if Even W.card then 1 else 0)) from fun _ => by ring]
  rw [← Finset.sum_mul, ← Finset.mul_sum]; ring

theorem finePairDensitySignedRule_mass_zero (a b : ℝ) (M : ℕ) :
    (∫ᵛ _e, (1 : ℝ) ∂<•finePairDensitySignedRule a b M) = 0 := by
  rw [finePairDensitySignedRule_integral a b M fun _ _ => 1]
  have hw : (∑ i : Fin 3, fineModulationWeight i) = 0 := by
    simpa only [pow_zero, mul_one, ite_true] using fineModulation_moment 0
  simp [hw]

theorem finePairDensitySignedRule_linear_zero {U : Type*} (a b : ℝ) (M : ℕ)
    (p ψ : U → ℝ) (u : U) :
    (∫ᵛ e, finePairDensityReset a b e.1 e.2 p ψ u
      ∂<•finePairDensitySignedRule a b M) = 0 := by
  rw [finePairDensitySignedRule_integral a b M fun z eps => finePairDensityReset a b z eps p ψ u]
  have haff (z c : ℝ) : (∑ i : Fin 3, fineModulationWeight i * (z + c * fineModulationNode i)) = 0 := by
    rw [fineModulation_eval fun eps => z + c * eps]; ring
  simp_rw [show ∀ z eps : ℝ, finePairDensityReset a b z eps p ψ u =
    z + (densityMargin a b z / b * p u * ψ u) * eps from fun _ _ => by unfold finePairDensityReset; ring, haff]
  simp

def finePairFieldReset {Z U : Type*} (a b : ℝ) (M : ℕ) (p : U → ℝ) (ψ : Z → U → ℝ)
    (e : Z × FinePairDensityIndex M) (u : U) : ℝ :=
  finePairDensityReset a b (finePairDensityAtom a b M e.2).1
    (finePairDensityAtom a b M e.2).2 p (ψ e.1) u

theorem finePairFieldReset_abs_le {Z U : Type*} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (M : ℕ) (p : U → ℝ) (hp : ∀ u, p u ∈ Icc a b) (ψ : Z → U → ℝ)
    (hψ : ∀ ζ u, |ψ ζ u| ≤ 1) (e : Z × FinePairDensityIndex M) (u : U) :
    |finePairFieldReset a b M p ψ e u| ≤ b := by
  have hh := finePairDensityReset_mem_interval a b ha hab _ _
    (exteriorNode_mem a b hab.le (M + 2) e.2.1) (fineModulationNode_bound e.2.2) p (ψ e.1) u (hp u) (hψ e.1 u)
  unfold finePairFieldReset finePairDensityAtom; rw [abs_of_nonneg (ha.le.trans hh.1)]; exact hh.2

abbrev FinePairPacketIndex (ι : Type*) (M q : ℕ) := FinePairDensityIndex M × HighResponseMarkIndex ι q

section FinePairPacket
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

def finePairPacketWeight (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  finePairDensityWeight a b M e.2.1 * highResponseMarkWeight C q (A e.1) e.2.2

theorem finePairPacketWeight_measurable (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable fun ζ => A ζ i j) :
    Measurable (finePairPacketWeight a b M q C A) :=
  measurable_from_prod_countable_left fun h => by
    dsimp [finePairPacketWeight, highResponseMarkWeight, covarianceWeight]; fun_prop

theorem finePairPacketWeight_integrable (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable fun ζ => A ζ i j) (hcost : Integrable (separatedMatrixCost A) σ) :
    Integrable (finePairPacketWeight a b M q C A) (σ.prod Measure.count) :=
  joint_finite_integrable σ _
    (fun h => by dsimp [finePairPacketWeight, highResponseMarkWeight, covarianceWeight]; fun_prop)
    fun h => by
      dsimp [finePairPacketWeight, highResponseMarkWeight, covarianceWeight]
      exact (((((separatedMatrix_entry_integrable σ A hA hcost h.2.1.1 h.2.1.2).const_mul
        (C ^ 2 / 2)).mul_const (fairSign h.2.2.1.1)).mul_const (fairSign h.2.2.1.2)).const_mul
          (responseWeight q h.2.2.2)).const_mul (finePairDensityWeight a b M h.1)

def finePairPacketSignedMeasure (σ : Measure Z) (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : SignedMeasure (Z × FinePairPacketIndex ι M q) :=
  (σ.prod Measure.count).withDensityᵥ (finePairPacketWeight a b M q C A)

theorem finePairPacketSignedMeasure_totalVariation (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable fun ζ => A ζ i j) (hcost : Integrable (separatedMatrixCost A) σ) :
    ((finePairPacketSignedMeasure σ a b M q C A).variation univ).toReal =
      (∑ h : FinePairDensityIndex M, |finePairDensityWeight a b M h|) *
        (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2) *
          (∫ ζ, separatedMatrixCost A ζ ∂σ) := by
  have hw := finePairPacketWeight_integrable σ a b M q C A hA hcost
  rw [finePairPacketSignedMeasure, Measure.variation_withDensityᵥ hw, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← integral_norm_eq_lintegral_enorm hw.aestronglyMeasurable, integral_prod _ hw.norm]
  have hvar (ζ : Z) : (∑ h : FinePairPacketIndex ι M q, |finePairPacketWeight a b M q C A (ζ, h)|) =
      (∑ h : FinePairDensityIndex M, |finePairDensityWeight a b M h|) *
        (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2) * separatedMatrixCost A ζ := by
    rw [Fintype.sum_prod_type]; simp only [finePairPacketWeight, abs_mul]
    simp_rw [← Finset.mul_sum, highResponseMark_variation]; rw [← Finset.sum_mul]
    unfold separatedMatrixCost; ring
  simp only [integral_count, Real.norm_eq_abs, hvar]; rw [integral_const_mul]

def finePairPacketObservable (a b : ℝ) (M q : ℕ) (C : ℝ) (c : ι → ℝ)
    (G : Z → ℝ → ℝ → ℝ) (Φ : (ι → ℝ) → ℝ)
    (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  G e.1 (finePairDensityAtom a b M e.2.1).1 (finePairDensityAtom a b M e.2.1).2 *
    Φ (coefficientReset c (highResponseMarkAtom C q e.2.2).2 (highResponseMarkAtom C q e.2.2).1)

lemma finePairPacketObservable_finite_action (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (c : ι → ℝ) (G : Z → ℝ → ℝ → ℝ) (Φ : (ι → ℝ) → ℝ) (ζ : Z) :
    (∑ h : FinePairPacketIndex ι M q, finePairPacketWeight a b M q C A (ζ, h) *
      finePairPacketObservable a b M q C c G Φ (ζ, h)) =
      (∫ᵛ e, G ζ e.1 e.2 ∂<•finePairDensitySignedRule a b M) * responseMatrixAction q C (A ζ) c Φ := by
  rw [Fintype.sum_prod_type, finePairDensitySignedRule, atomicSignedRule_integral]
  simp only [finePairPacketWeight, finePairPacketObservable]
  simp_rw [show ∀ (h : FinePairDensityIndex M) (v : HighResponseMarkIndex ι q),
    finePairDensityWeight a b M h * highResponseMarkWeight C q (A ζ) v *
      (G ζ (finePairDensityAtom a b M h).1 (finePairDensityAtom a b M h).2 *
        Φ (coefficientReset c (highResponseMarkAtom C q v).2 (highResponseMarkAtom C q v).1)) =
    (finePairDensityWeight a b M h * G ζ (finePairDensityAtom a b M h).1 (finePairDensityAtom a b M h).2) *
      (highResponseMarkWeight C q (A ζ) v *
        Φ (coefficientReset c (highResponseMarkAtom C q v).2 (highResponseMarkAtom C q v).1))
    from fun _ _ => by ring, ← Finset.mul_sum, highResponseMark_action]
  rw [← Finset.sum_mul]

theorem finePairPacketSignedMeasure_factor_integral (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable fun ζ => A ζ i j) (hcost : Integrable (separatedMatrixCost A) σ)
    (c : ι → ℝ) (G : Z → ℝ → ℝ → ℝ) (hG : ∀ z eps, Measurable fun ζ => G ζ z eps)
    (L : ℝ) (hL : 0 ≤ L) (hGbound : ∀ ζ h,
      |G ζ (finePairDensityAtom a b M h).1 (finePairDensityAtom a b M h).2| ≤ L)
    (Φ : (ι → ℝ) → ℝ) (R : ℝ) (hΦ : ∀ h : HighResponseMarkIndex ι q,
      |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)| ≤ R) :
    (∫ᵛ e, finePairPacketObservable a b M q C c G Φ e ∂<•finePairPacketSignedMeasure σ a b M q C A) =
      ∫ ζ, (∫ᵛ e, G ζ e.1 e.2 ∂<•finePairDensitySignedRule a b M) * responseMatrixAction q C (A ζ) c Φ ∂σ := by
  let f := finePairPacketObservable a b M q C c G Φ
  have hm : Measurable f := measurable_from_prod_countable_left fun h => by
    dsimp [f, finePairPacketObservable]; exact (hG _ _).mul_const _
  have hb (e : Z × FinePairPacketIndex ι M q) : ‖f e‖ ≤ L * R := by
    dsimp only [f, finePairPacketObservable]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hGbound e.1 e.2.1) (hΦ e.2.2) (abs_nonneg _) hL
  have hw := finePairPacketWeight_integrable σ a b M q C A hA hcost
  rw [finePairPacketSignedMeasure, signedDensity_integral _ _ hw
      (finePairPacketWeight_measurable a b M q C A hA) f hm (L * R) hb,
    integral_prod _ (hw.mul_bdd hm.aestronglyMeasurable (Filter.Eventually.of_forall hb))]
  simp only [integral_count, f, finePairPacketObservable_finite_action]

theorem finePairPacketSignedMeasure_pair_action {U : Type*} (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (M q : ℕ) (hM : 2 ≤ M) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable fun ζ => A ζ i j)
    (hcost : Integrable (separatedMatrixCost A) σ) (c : ι → ℝ)
    (p : U → ℝ) (hp : ∀ u, p u ∈ Icc a b) (ψ : Z → U → ℝ)
    (hmψ : ∀ u, Measurable fun ζ => ψ ζ u) (hψ : ∀ ζ u, |ψ ζ u| ≤ 1)
    (u v : U) (Φ : (ι → ℝ) → ℝ) (R : ℝ) (hΦ : ∀ h : HighResponseMarkIndex ι q,
      |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)| ≤ R) :
    (∫ᵛ e, finePairPacketObservable a b M q C c
      (fun ζ z eps => finePairDensityReset a b z eps p (ψ ζ) u *
        finePairDensityReset a b z eps p (ψ ζ) v) Φ e
      ∂<•finePairPacketSignedMeasure σ a b M q C A) =
      p u * p v * (∫ ζ, ψ ζ u * ψ ζ v * responseMatrixAction q C (A ζ) c Φ ∂σ) := by
  have hm (z eps : ℝ) (w : U) : Measurable fun ζ => finePairDensityReset a b z eps p (ψ ζ) w :=
    measurable_const.add ((hmψ w).const_mul _)
  rw [finePairPacketSignedMeasure_factor_integral σ a b M q C A hA hcost c
    (fun ζ z eps => finePairDensityReset a b z eps p (ψ ζ) u * finePairDensityReset a b z eps p (ψ ζ) v)
    (fun z eps => (hm z eps u).mul (hm z eps v)) (b ^ 2) (by positivity)
    (fun ζ h => by
      rw [abs_mul, pow_two]
      exact mul_le_mul (finePairFieldReset_abs_le a b ha hab M p hp ψ hψ (ζ, h) u)
        (finePairFieldReset_abs_le a b ha hab M p hp ψ hψ (ζ, h) v) (abs_nonneg _) (ha.trans hab).le)
    Φ R hΦ]
  have hpair (ζ : Z) : (∫ᵛ e, finePairDensityReset a b e.1 e.2 p (ψ ζ) u *
      finePairDensityReset a b e.1 e.2 p (ψ ζ) v ∂<•finePairDensitySignedRule a b M) =
      p u * p v * ψ ζ u * ψ ζ v := by
    rw [finePairDensitySignedRule_integral a b M
      fun z eps => finePairDensityReset a b z eps p (ψ ζ) u * finePairDensityReset a b z eps p (ψ ζ) v]
    have hq (z c c' : ℝ) : (∑ i : Fin 3, fineModulationWeight i *
        ((z + c * fineModulationNode i) * (z + c' * fineModulationNode i))) = c * c' := by
      rw [fineModulation_eval fun eps => (z + c * eps) * (z + c' * eps)]; ring
    simp_rw [show ∀ (z eps : ℝ) (w : U), finePairDensityReset a b z eps p (ψ ζ) w =
      z + (densityMargin a b z / b * p w * ψ ζ w) * eps from fun _ _ _ => by unfold finePairDensityReset; ring, hq]
    have hc := densityCountCoefficient_exact a b ha hab M 2 2 (by omega) (by omega) hM
    simp only [densityCountCoefficient, Nat.sub_self, pow_zero, one_mul, ite_true] at hc
    have hθ : densityMargin a b 0 ^ 2 ≠ 0 := pow_ne_zero _ (densityMargin_zero_ne a b ha hab)
    have hs : (∑ j : Fin (M + 3), exteriorWeight a b (M + 2) j *
        densityMargin a b (exteriorNode a b (M + 2) j) ^ 2) = densityMargin a b 0 ^ 2 :=
      (div_eq_iff hθ).mp hc |>.trans (one_mul _)
    simp_rw [show ∀ j : Fin (M + 3), exteriorWeight a b (M + 2) j *
        ((densityMargin a b (exteriorNode a b (M + 2) j) / b * p u * ψ ζ u) *
         (densityMargin a b (exteriorNode a b (M + 2) j) / b * p v * ψ ζ v)) =
        exteriorWeight a b (M + 2) j * densityMargin a b (exteriorNode a b (M + 2) j) ^ 2 *
        ((p u * p v * ψ ζ u * ψ ζ v) / b ^ 2) from fun _ => by ring]
    rw [← Finset.sum_mul, hs]; unfold finePairDensityPrefactor
    field_simp [hθ, densityMargin_zero_ne a b ha hab, (ha.trans hab).ne']
  simp_rw [hpair, show ∀ ζ : Z, p u * p v * ψ ζ u * ψ ζ v * responseMatrixAction q C (A ζ) c Φ =
    (p u * p v) * (ψ ζ u * ψ ζ v * responseMatrixAction q C (A ζ) c Φ) from fun _ => by ring]
  exact integral_const_mul _ _

def finePairPacketMarkMass (σ : Measure Z) (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ) : ℝ :=
  signedMarkMass (σ.prod Measure.count) (finePairPacketWeight a b M q C A)

def finePairPacketAbsoluteLaw (σ : Measure Z) (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : Measure (Z × FinePairPacketIndex ι M q) :=
  absoluteMarkLaw (σ.prod Measure.count) (finePairPacketWeight a b M q C A)

def finePairPacketActivation (σ : Measure Z) (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : Z × FinePairPacketIndex ι M q → ℝ :=
  absoluteActivation (σ.prod Measure.count) (finePairPacketWeight a b M q C A)

def finePairPacketIntercept (a b : ℝ) (M q : ℕ) (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  (finePairDensityAtom a b M e.2.1).1

def finePairPacketSlope (a b : ℝ) (M q : ℕ) (ψ : Z → ℝ) (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  densityMargin a b (finePairPacketIntercept a b M q e) / b *
    (finePairDensityAtom a b M e.2.1).2 * ψ e.1

def finePairPacketResponseVector (M q : ℕ) (C : ℝ) (e : Z × FinePairPacketIndex ι M q) : ι → ℝ :=
  (highResponseMarkAtom C q e.2.2).2

def finePairPacketResponseTime (M q : ℕ) (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  (highResponseMarkAtom 0 q e.2.2).1

theorem finePairPacketIntercept_measurable (a b : ℝ) (M q : ℕ) :
    Measurable (finePairPacketIntercept (Z := Z) (ι := ι) a b M q) :=
  measurable_from_prod_countable_left fun _ => by dsimp [finePairPacketIntercept]; exact measurable_const

theorem finePairPacketSlope_joint_measurable {U : Type*} [MeasurableSpace U]
    (a b : ℝ) (M q : ℕ) (ψ : Z → U → ℝ)
    (hψ : Measurable fun zu : Z × U => ψ zu.1 zu.2) :
    Measurable fun eu : (Z × FinePairPacketIndex ι M q) × U =>
      finePairPacketSlope a b M q (fun ζ => ψ ζ eu.2) eu.1 :=
  ((measurable_of_countable fun h : FinePairPacketIndex ι M q =>
    densityMargin a b (finePairDensityAtom a b M h.1).1 / b *
      (finePairDensityAtom a b M h.1).2).comp (measurable_snd.comp measurable_fst)).mul
    (hψ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

theorem finePairPacketIntercept_mem (a b : ℝ) (hab : a ≤ b) (M q : ℕ)
    (e : Z × FinePairPacketIndex ι M q) : finePairPacketIntercept a b M q e ∈ Icc a b :=
  exteriorNode_mem a b hab (M + 2) e.2.1.1

theorem finePairPacketSlope_bound (a b : ℝ) (ha : 0 < a) (hab : a < b) (M q : ℕ)
    (ψ : Z → ℝ) (hψ : ∀ ζ, |ψ ζ| ≤ 1) (e : Z × FinePairPacketIndex ι M q) :
    |finePairPacketSlope a b M q ψ e| ≤ (b - a) / (4 * b) := by
  simpa [finePairPacketSlope, finePairPacketIntercept, mul_assoc] using
    localDensityReset_slope_bound a b ha hab 1 (by omega)
      (finePairDensityAtom a b M e.2.1).1 (exteriorNode_mem a b hab.le (M + 2) e.2.1.1)
      (fun _ => (finePairDensityAtom a b M e.2.1).2) (fun _ => fineModulationNode_bound e.2.1.2)
      (fun _ : Unit => fun _ => ψ e.1) () fun _ => hψ e.1

theorem finePairPacketAbsoluteLaw_probability
    (σ : Measure Z) [IsFiniteMeasure σ] (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable fun ζ => A ζ i j)
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < finePairPacketMarkMass σ a b M q C A) :
    IsProbabilityMeasure (finePairPacketAbsoluteLaw σ a b M q C A) :=
  absoluteMarkLaw_probability _ _ (finePairPacketWeight_integrable σ a b M q C A hA hcost) hpos

theorem finePairPacketActivation_centered
    (σ : Measure Z) [IsFiniteMeasure σ] (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable fun ζ => A ζ i j)
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < finePairPacketMarkMass σ a b M q C A) :
    (∫ e, finePairPacketActivation σ a b M q C A e ∂finePairPacketAbsoluteLaw σ a b M q C A) = 0 := by
  apply absoluteActivation_centered _ _ (finePairPacketWeight_measurable a b M q C A hA) hpos
  rw [integral_prod _ (finePairPacketWeight_integrable σ a b M q C A hA hcost)]
  simp only [integral_count]
  have hz (ζ : Z) : (∑ h : FinePairPacketIndex ι M q, finePairPacketWeight a b M q C A (ζ, h)) = 0 := by
    simpa only [finePairPacketObservable, mul_one, responseMatrixAction_zero_mass, mul_zero] using
      finePairPacketObservable_finite_action a b M q C A (fun _ => 0) (fun _ _ _ => 1) (fun _ => 1) ζ
  simp only [hz, integral_zero]

theorem finePairPacketAbsoluteLaw_slope_integral_zero
    (σ : Measure Z) [IsFiniteMeasure σ] (a b : ℝ) (M q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable fun ζ => A ζ i j)
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < finePairPacketMarkMass σ a b M q C A)
    (ha : 0 < a) (hab : a < b) (ψ : Z → ℝ) (hmψ : Measurable ψ) (hψ : ∀ ζ, |ψ ζ| ≤ 1) :
    (∫ e, finePairPacketSlope a b M q ψ e ∂finePairPacketAbsoluteLaw σ a b M q C A) = 0 := by
  have hsm : Measurable (finePairPacketSlope (ι := ι) a b M q ψ) :=
    measurable_from_prod_countable_left fun _ => by
      dsimp [finePairPacketSlope, finePairPacketIntercept]; exact hmψ.const_mul _
  have hi := (finePairPacketWeight_integrable σ a b M q C A hA hcost).abs.mul_bdd hsm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun e => by
      simpa only [Real.norm_eq_abs] using finePairPacketSlope_bound a b ha hab M q ψ hψ e)
  rw [finePairPacketAbsoluteLaw, absoluteMarkLaw_integral _ _
    (finePairPacketWeight_measurable a b M q C A hA) hpos, integral_prod _ hi]
  let refl : Equiv.Perm (FinePairPacketIndex ι M q) :=
    Equiv.prodCongr (Equiv.prodCongr (Equiv.refl _) Fin.revPerm) (Equiv.refl _)
  have hsum0 (ζ : Z) : (∑ h : FinePairPacketIndex ι M q,
      |finePairPacketWeight a b M q C A (ζ, h)| * finePairPacketSlope a b M q ψ (ζ, h)) = 0 :=
    finite_even_odd_sum_zero refl _ _
      (fun h => by
        have hw : ∀ i : Fin 3, |fineModulationWeight i.rev| = |fineModulationWeight i| := fun i => by
          fin_cases i <;> norm_num [fineModulationWeight, Fin.rev]
        simp [refl, finePairPacketWeight, finePairDensityWeight, abs_mul, hw])
      fun h => by
        have hn : ∀ i : Fin 3, fineModulationNode i.rev = -fineModulationNode i := fun i => by
          fin_cases i <;> norm_num [fineModulationNode, Fin.rev]
        simp only [refl, finePairPacketSlope, finePairPacketIntercept, finePairDensityAtom,
          Equiv.prodCongr_apply, Prod.map_apply, Prod.map_fst, Prod.map_snd,
          Equiv.refl_apply, Fin.revPerm_apply, hn]
        ring
  simp only [integral_count, hsum0, integral_zero, zero_div]

end FinePairPacket
end FrameOrthogonalityAndPackets

-- ============================================================================
-- 3. Row Reference Union, Affine History, Heap Fold, MGF, and Observables
-- ============================================================================

section RowUnionHistoryAndObservables
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def highCenterResolutionThreshold {d : ℕ} (C : ModelConstants d) : ℝ :=
  max 2 (highCenterRadius C)⁻¹

theorem highCenterResolution_guards {d : ℕ} (C : ModelConstants d) (M : ℝ)
    (hM : highCenterResolutionThreshold C ≤ M) : 2 ≤ M ∧ 1 / M ≤ highCenterRadius C := by
  have hM2 : 2 ≤ M := (le_max_left _ _).trans hM
  have hMr : (highCenterRadius C)⁻¹ ≤ M := (le_max_right _ _).trans hM
  refine ⟨hM2, (div_le_iff₀ (by linarith)).mpr ?_⟩
  have hh := mul_le_mul_of_nonneg_left hMr (highCenterRadius_pos C).le
  rw [mul_inv_cancel₀ (highCenterRadius_pos C).ne'] at hh
  nlinarith

section RowUnion
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] {E : J → Type*} [∀ j, MeasurableSpace (E j)]

theorem rowSigmaMk_measurable (j : J) : Measurable (@Sigma.mk J E j) :=
  Measurable.of_le_map (iInf_le _ j)

theorem rowSigmaFunction_measurable (F : (j : J) → E j → ℝ)
    (hF : ∀ j, Measurable (F j)) : Measurable fun e : Sigma E => F e.1 e.2 := by
  intro s hs
  change MeasurableSet[⨅ j, MeasurableSpace.map (Sigma.mk j)
    (inferInstance : MeasurableSpace (E j))] ((fun e : Sigma E => F e.1 e.2) ⁻¹' s)
  exact MeasurableSpace.measurableSet_iInf.mpr fun j => hF j hs

theorem highRowReferenceUnion_standardBorel [∀ j, StandardBorelSpace (E j)] :
    StandardBorelSpace (Sigma E) := by
  letI := fun j => upgradeStandardBorel (E j)
  letI : BorelSpace (Sigma E) := historySigma_borelSpace
  infer_instance

def highRowTotalMass (B : J → ℝ) : ℝ := ∑ j, B j
def highRowSelectionProbability (B : J → ℝ) (j : J) : ℝ := B j / highRowTotalMass B

def highRowReferenceUnion (π : (j : J) → Measure (E j)) (B : J → ℝ) : Measure (Sigma E) :=
  ∑ j, ENNReal.ofReal (highRowSelectionProbability B j) • (π j).map (Sigma.mk j)

lemma highRowReferenceUnion_probability (π : (j : J) → Measure (E j))
    [∀ j, IsProbabilityMeasure (π j)] (B : J → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hTotal : 0 < highRowTotalMass B) : IsProbabilityMeasure (highRowReferenceUnion π B) := by
  constructor
  rw [highRowReferenceUnion, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.map_apply (rowSigmaMk_measurable _) MeasurableSet.univ,
    preimage_univ, measure_univ, smul_eq_mul, mul_one]
  unfold highRowSelectionProbability
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => div_nonneg (hB j) (by unfold highRowTotalMass; exact Finset.sum_nonneg fun _ _ => hB _),
    ← Finset.sum_div, show (∑ j, B j) = highRowTotalMass B from rfl, div_self hTotal.ne']
  norm_num

theorem highRowReferenceUnion_integrable (π : (j : J) → Measure (E j)) (B : J → ℝ)
    (F : Sigma E → ℝ) (hF : Measurable F)
    (hInt : ∀ j, Integrable (fun e => F ⟨j, e⟩) (π j)) :
    Integrable F (highRowReferenceUnion π B) :=
  integrable_finsetSum_measure.mpr fun j _ =>
    ((integrable_map_measure hF.aestronglyMeasurable (rowSigmaMk_measurable j).aemeasurable).mpr
      (hInt j)).smul_measure ENNReal.ofReal_ne_top

lemma highRowReferenceUnion_integral (π : (j : J) → Measure (E j)) (B : J → ℝ)
    (hB : ∀ j, 0 ≤ B j) (F : Sigma E → ℝ) (hF : Measurable F)
    (hInt : ∀ j, Integrable (fun e => F ⟨j, e⟩) (π j)) :
    (∫ e, F e ∂highRowReferenceUnion π B) =
      ∑ j, highRowSelectionProbability B j * ∫ e, F ⟨j, e⟩ ∂π j := by
  unfold highRowReferenceUnion
  rw [integral_finsetSum_measure fun j _ =>
    ((integrable_map_measure hF.aestronglyMeasurable (rowSigmaMk_measurable j).aemeasurable).mpr
      (hInt j)).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold highRowSelectionProbability
  rw [integral_smul_measure, integral_map (rowSigmaMk_measurable j).aemeasurable hF.aestronglyMeasurable,
    ENNReal.toReal_ofReal (div_nonneg (hB j) (by unfold highRowTotalMass; exact Finset.sum_nonneg fun _ _ => hB _)), smul_eq_mul]

def highRowUnionActivation (B : J → ℝ) (w : (j : J) → E j → ℝ) (e : Sigma E) : ℝ :=
  w e.1 e.2 / highRowSelectionProbability B e.1

theorem highRowUnionActivation_measurable (B : J → ℝ) (w : (j : J) → E j → ℝ)
    (hw : ∀ j, Measurable (w j)) : Measurable (highRowUnionActivation B w) :=
  rowSigmaFunction_measurable _ fun j => (hw j).div_const _

theorem highRowUnionActivation_integrable (π : (j : J) → Measure (E j))
    (B : J → ℝ) (w : (j : J) → E j → ℝ) (hw : ∀ j, Measurable (w j))
    (hInt : ∀ j, Integrable (w j) (π j)) :
    Integrable (highRowUnionActivation B w) (highRowReferenceUnion π B) :=
  highRowReferenceUnion_integrable π B _ (highRowUnionActivation_measurable B w hw) fun j => by
    simpa only [highRowUnionActivation] using (hInt j).div_const (highRowSelectionProbability B j)

theorem highRowUnionActivation_action (π : (j : J) → Measure (E j))
    (B : J → ℝ) (hB : ∀ j, 0 < B j) (hTotal : 0 < highRowTotalMass B)
    (w : (j : J) → E j → ℝ) (hw : ∀ j, Measurable (w j))
    (F : Sigma E → ℝ) (hF : Measurable F)
    (hInt : ∀ j, Integrable (fun e => w j e * F ⟨j, e⟩) (π j)) :
    (∫ e, highRowUnionActivation B w e * F e ∂highRowReferenceUnion π B) =
      ∑ j, ∫ e, w j e * F ⟨j, e⟩ ∂π j := by
  have he (j : J) : (fun e : E j => highRowUnionActivation B w ⟨j, e⟩ * F ⟨j, e⟩) =
      fun e => (w j e * F ⟨j, e⟩) / highRowSelectionProbability B j := by
    funext e; unfold highRowUnionActivation; ring
  rw [highRowReferenceUnion_integral π B (fun j => (hB j).le)
    (fun e => highRowUnionActivation B w e * F e)
    ((highRowUnionActivation_measurable B w hw).mul hF)
    fun j => by rw [he j]; exact (hInt j).div_const _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [he j, integral_div]
  exact mul_div_cancel₀ _ (div_pos (hB j) hTotal).ne'

def highCenteredRowUnionLaw (π : (j : J) → Measure (E j)) (B : J → ℝ) (δ : ℝ) :
    Measure ((Sigma E) ⊕ Unit) := balancedReferenceLaw (highRowReferenceUnion π B) δ

def highCenteredRowUnionActivation (B : J → ℝ) (w : (j : J) → E j → ℝ) (δ : ℝ) :
    (Sigma E) ⊕ Unit → ℝ := balancedActivation (highRowUnionActivation B w) δ

def highCenteredRowUnionIntercept (π : (j : J) → Measure (E j)) (B : J → ℝ)
    (intercept : (j : J) → E j → ℝ) (δ : ℝ) : (Sigma E) ⊕ Unit → ℝ :=
  balancedIntercept (fun e : Sigma E => intercept e.1 e.2) δ
    (∫ e : Sigma E, intercept e.1 e.2 ∂highRowReferenceUnion π B)

def highCenteredRowUnionSlope (slope : (j : J) → E j → ℝ) : (Sigma E) ⊕ Unit → ℝ :=
  balancedSlope fun e : Sigma E => slope e.1 e.2

theorem highCenteredRowUnionLaw_probability (π : (j : J) → Measure (E j))
    [∀ j, IsProbabilityMeasure (π j)] (B : J → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hTotal : 0 < highRowTotalMass B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    IsProbabilityMeasure (highCenteredRowUnionLaw π B δ) := by
  letI := highRowReferenceUnion_probability π B hB hTotal
  exact balancedReferenceLaw_probability _ δ hδ0 hδ1

theorem highCenteredRowUnionActivation_centered (π : (j : J) → Measure (E j))
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (w : (j : J) → E j → ℝ)
    (hw : ∀ j, Measurable (w j)) (hInt : ∀ j, Integrable (w j) (π j))
    (hCenter : ∀ j, (∫ e, w j e ∂π j) = 0)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫ e, highCenteredRowUnionActivation B w δ e ∂highCenteredRowUnionLaw π B δ) = 0 := by
  refine balancedActivation_integral_zero _ δ hδ hδ1 _ (highRowUnionActivation_measurable B w hw)
    (highRowUnionActivation_integrable π B w hw hInt) ?_
  rw [highRowReferenceUnion_integral π B hB _ (highRowUnionActivation_measurable B w hw) fun j => by
    simpa only [highRowUnionActivation] using (hInt j).div_const (highRowSelectionProbability B j)]
  simp only [highRowUnionActivation, integral_div, hCenter, zero_div, mul_zero, Finset.sum_const_zero]

theorem highCenteredRowUnionActivation_bound (B : J → ℝ) (hB : ∀ j, 0 < B j)
    (hTotal : 0 < highRowTotalMass B) (w : (j : J) → E j → ℝ)
    (hw : ∀ j e, |w j e| ≤ B j) (δ : ℝ) (hδ : 0 < δ) (e : (Sigma E) ⊕ Unit) :
    |highCenteredRowUnionActivation B w δ e| ≤ highRowTotalMass B / δ := by
  apply balancedActivation_bound _ δ _ hδ hTotal.le
  intro e
  have hα : 0 < highRowSelectionProbability B e.1 := div_pos (hB e.1) hTotal
  unfold highRowUnionActivation
  rw [abs_div, abs_of_pos hα]
  refine (div_le_iff₀ hα).mpr ?_
  rw [show highRowTotalMass B * highRowSelectionProbability B e.1 = B e.1 by
    unfold highRowSelectionProbability; field_simp [hTotal.ne']]
  exact hw e.1 e.2

theorem highCenteredRowUnionActivation_measurable (B : J → ℝ)
    (w : (j : J) → E j → ℝ) (hw : ∀ j, Measurable (w j)) (δ : ℝ) :
    Measurable (highCenteredRowUnionActivation B w δ) :=
  balancedActivation_measurable _ (highRowUnionActivation_measurable B w hw) δ

theorem highCenteredRowUnionSlope_measurable (slope : (j : J) → E j → ℝ)
    (hSlope : ∀ j, Measurable (slope j)) : Measurable (highCenteredRowUnionSlope slope) :=
  balancedSlope_measurable _ (rowSigmaFunction_measurable slope hSlope)

theorem highCenteredRowUnionIntercept_measurable (π : (j : J) → Measure (E j)) (B : J → ℝ)
    (intercept : (j : J) → E j → ℝ) (hIntercept : ∀ j, Measurable (intercept j)) (δ : ℝ) :
    Measurable (highCenteredRowUnionIntercept π B intercept δ) :=
  balancedIntercept_measurable _ (rowSigmaFunction_measurable intercept hIntercept) δ _

theorem highCenteredRowUnionSlope_integral_zero (π : (j : J) → Measure (E j))
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (hTotal : 0 < highRowTotalMass B)
    (slope : (j : J) → E j → ℝ) (hSlope : ∀ j, Measurable (slope j))
    (hiSlope : ∀ j, Integrable (slope j) (π j))
    (hCenter : ∀ j, (∫ e, slope j e ∂π j) = 0)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (∫ e, highCenteredRowUnionSlope slope e ∂highCenteredRowUnionLaw π B δ) = 0 := by
  refine balancedSlope_integral_zero _ δ hδ0 hδ1 _ (rowSigmaFunction_measurable slope hSlope)
    (highRowReferenceUnion_integrable π B _ (rowSigmaFunction_measurable slope hSlope) hiSlope) ?_
  rw [highRowReferenceUnion_integral π B hB _ (rowSigmaFunction_measurable slope hSlope) hiSlope]
  simp only [hCenter, mul_zero, Finset.sum_const_zero]

theorem highCenteredRowUnionIntercept_integral_one (π : (j : J) → Measure (E j))
    [∀ j, IsProbabilityMeasure (π j)] (B : J → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hTotal : 0 < highRowTotalMass B)
    (intercept : (j : J) → E j → ℝ) (hIntercept : ∀ j, Measurable (intercept j))
    (a b : ℝ) (hBound : ∀ j e, intercept j e ∈ Icc a b)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (∫ e, highCenteredRowUnionIntercept π B intercept δ e ∂highCenteredRowUnionLaw π B δ) = 1 := by
  letI := highRowReferenceUnion_probability π B hB hTotal
  exact balancedIntercept_integral_one _ δ hδ0 hδ1 _
    (rowSigmaFunction_measurable intercept hIntercept)
    (boundedIntercept_integrable (highRowReferenceUnion π B) _
      (rowSigmaFunction_measurable intercept hIntercept) a b fun e => hBound e.1 e.2)

theorem highCenteredRowUnion_reset_source_legal {d : ℕ} (C : ModelConstants d)
    (π : (j : J) → Measure (E j)) [∀ j, IsProbabilityMeasure (π j)]
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (hTotal : 0 < highRowTotalMass B)
    (slope intercept : (j : J) → E j → ℝ) (hIntercept : ∀ j, Measurable (intercept j))
    (M : ℝ) (hM : highCenterResolutionThreshold C ≤ M)
    (hBound : ∀ j e, intercept j e ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M))
    (hlegal : ∀ j e p, p ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M) →
      slope j e*p+intercept j e ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M))
    (e : (Sigma E) ⊕ Unit) (p : ℝ)
    (hp : p ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M)) :
    highCenteredRowUnionSlope slope e*p+highCenteredRowUnionIntercept π B intercept (highCenterMix C) e ∈
      Icc (C.densityLower+1/M) (C.densityUpper-1/M) := by
  cases e with
  | inl e => exact hlegal e.1 e.2 p hp
  | inr u =>
    letI := highRowReferenceUnion_probability π B hB hTotal
    have hg := highCenterResolution_guards C M hM
    have hq := boundedIntercept_mean_mem (highRowReferenceUnion π B)
      (fun e : Sigma E => intercept e.1 e.2) (rowSigmaFunction_measurable intercept hIntercept)
      (C.densityLower+1/M) (C.densityUpper-1/M) fun e => hBound e.1 e.2
    rw [show highCenteredRowUnionSlope slope (Sum.inr u) * p +
        highCenteredRowUnionIntercept π B intercept (highCenterMix C) (Sum.inr u) =
      highCenteredRowUnionIntercept π B intercept (highCenterMix C) (Sum.inr u) by
      simp [highCenteredRowUnionSlope, balancedSlope]]
    exact sourceBalancedResetAnchor_mem C M _ (by linarith) hg.2 hq

end RowUnion

def finiteAffineHistory {J E : Type*} (slope offset : J → E → ℝ)
    (n : ℕ) (labels : Fin n → J) (marks : Fin n → E) : ℝ :=
  (List.ofFn fun i : Fin n => i).foldl
    (fun value i => slope (labels i) (marks i) * value + offset (labels i) (marks i)) 1

lemma finiteAffineHistory_succ {J E : Type*} (slope offset : J → E → ℝ)
    (n : ℕ) (labels : Fin (n + 1) → J) (marks : Fin (n + 1) → E) :
    finiteAffineHistory slope offset (n + 1) labels marks =
      slope (labels (Fin.last n)) (marks (Fin.last n)) *
        finiteAffineHistory slope offset n (fun i => labels i.castSucc) (fun i => marks i.castSucc) +
      offset (labels (Fin.last n)) (marks (Fin.last n)) := by
  unfold finiteAffineHistory
  rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
  congr 2
  rw [show (List.ofFn fun i : Fin n => i.castSucc) = (List.ofFn fun i : Fin n => i).map Fin.castSucc by
    rw [List.map_ofFn]; rfl, List.foldl_map]

theorem finiteAffineHistory_integral_one {J E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (slope offset : J → E → ℝ)
    (hs : ∀ j, Integrable (slope j) π) (ho : ∀ j, Integrable (offset j) π)
    (hmean : ∀ j, (∫ e, slope j e ∂π) + (∫ e, offset j e ∂π) = 1)
    (n : ℕ) (labels : Fin n → J) :
    (∫ marks, finiteAffineHistory slope offset n labels marks
      ∂Measure.pi fun _ : Fin n => π) = 1 := by
  have hint : ∀ (m : ℕ) (lbl : Fin m → J),
      Integrable (finiteAffineHistory slope offset m lbl) (Measure.pi fun _ : Fin m => π) := by
    intro m; induction m with
    | zero => intro _; exact integrable_const _
    | succ m ih =>
      intro lbl
      apply ((historyFiniteMarkAppendEquiv_preserving m π).integrable_comp_emb
        (historyFiniteMarkAppendEquiv m).measurableEmbedding).mp
      convert ((hs (lbl (Fin.last m))).mul_prod (ih fun i => lbl i.castSucc)).add
        ((ho (lbl (Fin.last m))).comp_fst _) using 1
      funext ⟨_, _⟩
      simp only [Function.comp_apply, finiteAffineHistory_succ,
        historyFiniteMarkAppendEquiv_last, historyFiniteMarkAppendEquiv_old]; rfl
  induction n with
  | zero => simp [finiteAffineHistory]
  | succ n ih =>
    let j := labels (Fin.last n)
    let f := finiteAffineHistory slope offset n fun i => labels i.castSucc
    rw [← (historyFiniteMarkAppendEquiv_preserving n π).integral_comp
      (historyFiniteMarkAppendEquiv n).measurableEmbedding,
      show (fun p : E × (Fin n → E) => finiteAffineHistory slope offset (n + 1) labels (historyFiniteMarkAppendEquiv n p)) =
        fun p => slope j p.1 * f p.2 + offset j p.1 from funext fun ⟨_, _⟩ => by
          simp only [finiteAffineHistory_succ, historyFiniteMarkAppendEquiv_last, historyFiniteMarkAppendEquiv_old]; rfl,
      integral_add ((hs j).mul_prod (hint n _)) ((ho j).comp_fst _), integral_prod_mul, integral_fun_fst]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, ih, mul_one]
    exact hmean j

section RawDensityLocality
attribute [local instance] Classical.propDecidable

def affineRawHistory {J X E C I : Type*} [DecidableEq J]
    (patch : J → Set X) (slope intercept : J → E → X → ℝ)
    (response : J → E → C → C) (labels : I → J) (indices : List I)
    (marks : I → E) (initial : (X → ℝ) × (J → C)) : (X → ℝ) × (J → C) :=
  indices.foldl (fun state i => rawPatchUpdate (labels i) (patch (labels i))
    (slope (labels i) (marks i)) (intercept (labels i) (marks i))
    (response (labels i) (marks i)) state) initial

theorem affineRawHistory_density_interval {J X E C I : Type*} [DecidableEq J]
    (patch : J → Set X) (slope intercept : J → E → X → ℝ) (response : J → E → C → C)
    (labels : I → J) (indices : List I) (marks : I → E) (a b : ℝ)
    (hlegal : ∀ j e x v, v ∈ Icc a b → slope j e x * v + intercept j e x ∈ Icc a b)
    (initial : (X → ℝ) × (J → C)) (hi : ∀ x, initial.1 x ∈ Icc a b) :
    ∀ x, (affineRawHistory patch slope intercept response labels indices marks initial).1 x ∈ Icc a b := by
  induction indices generalizing initial with
  | nil => exact hi
  | cons i indices ih =>
    refine ih _ fun x => ?_
    change (if x ∈ patch (labels i) then slope (labels i) (marks i) x * initial.1 x +
      intercept (labels i) (marks i) x else initial.1 x) ∈ Icc a b
    split_ifs
    · exact hlegal _ _ _ _ (hi x)
    · exact hi x

def highAffineMarkedMass {E C : Type*} (d k : ℕ) [NeZero k]
    [LinearOrder (HighWindowLabels d k)] (dependent : HighWindowLabels d k → HighWindowLabels d k → Prop)
    (slope intercept : HighWindowLabels d k → E → Covariate d → ℝ)
    (response : HighWindowLabels d k → E → C → C)
    (initial : (Covariate d → ℝ) × (HighWindowLabels d k → C))
    (h : HistoryMarked dependent E) : ℝ :=
  ∫ x, (historyMarkedRawState dependent
    (fun j e state => rawPatchUpdate j (highTorusPatch d k j) (slope j e) (intercept j e)
      (response j e) state) initial h).1 x ∂cubeVolume d

theorem highAffineMarkedMass_block_oscillation {E C : Type*}
    (d k : ℕ) [NeZero k] [LinearOrder (HighWindowLabels d k)] (hk : 2 ≤ k)
    (dependent : HighWindowLabels d k → HighWindowLabels d k → Prop)
    (slope intercept : HighWindowLabels d k → E → Covariate d → ℝ)
    (hSlope : ∀ j e, Measurable (slope j e)) (hIntercept : ∀ j e, Measurable (intercept j e))
    (response : HighWindowLabels d k → E → C → C)
    (a b : ℝ) (hab : a ≤ b)
    (hlegal : ∀ l e x v, v ∈ Icc a b → slope l e x * v + intercept l e x ∈ Icc a b)
    (initial : (Covariate d → ℝ) × (HighWindowLabels d k → C))
    (him : Measurable initial.1) (hi : ∀ x, initial.1 x ∈ Icc a b)
    (g : HistoryShape fun l j => ¬ dependent l j)
    (marks marks' : Fin (historyShapeLength dependent g) → E) (j : HighWindowLabels d k)
    (hm : ∀ i, historyShapeCanonicalLabels dependent g i ≠ j → marks i = marks' i) :
    |highAffineMarkedMass d k dependent slope intercept response initial ⟨g, marks⟩ -
      highAffineMarkedMass d k dependent slope intercept response initial ⟨g, marks'⟩| ≤
        (2 / (k : ℝ))^d * (b-a) := by
  let _ := cubeVolume_isProbability d
  let n := historyShapeLength dependent g
  let labels := historyShapeCanonicalLabels dependent g
  let indices := List.ofFn fun i : Fin n => i
  let p := (affineRawHistory (highTorusPatch d k) slope intercept response labels indices marks initial).1
  let p' := (affineRawHistory (highTorusPatch d k) slope intercept response labels indices marks' initial).1
  have hdMeas (mk : Fin n → E) :
      Measurable (affineRawHistory (highTorusPatch d k) slope intercept response labels indices mk initial).1 := by
    suffices ∀ (ind : List (Fin n)) (init : (Covariate d → ℝ) × (HighWindowLabels d k → C)),
        Measurable init.1 →
        Measurable (affineRawHistory (highTorusPatch d k) slope intercept response labels ind mk init).1 from
      this indices initial him
    intro ind; induction ind with
    | nil => intro _ h0; exact h0
    | cons i ind ih =>
      intro init h0; simp only [affineRawHistory, List.foldl_cons]; refine ih _ ?_
      change Measurable fun x => if x ∈ highTorusPatch d k (labels i) then
        slope (labels i) (mk i) x * init.1 x + intercept (labels i) (mk i) x else init.1 x
      exact Measurable.ite (highTorusPatch_measurableSet d k _) (((hSlope _ _).mul h0).add (hIntercept _ _)) h0
  have hout (x : Covariate d) (hx : x ∉ highTorusPatch d k j) : p x = p' x := by
    suffices ∀ (ind : List (Fin n)) (init init' : (Covariate d → ℝ) × (HighWindowLabels d k → C)),
        init.1 x = init'.1 x →
        (affineRawHistory (highTorusPatch d k) slope intercept response labels ind marks init).1 x =
          (affineRawHistory (highTorusPatch d k) slope intercept response labels ind marks' init').1 x from
      this indices initial initial rfl
    intro ind; induction ind with
    | nil => intro _ _ h0; exact h0
    | cons i ind ih =>
      intro init init' h0; simp only [affineRawHistory, List.foldl_cons]; refine ih _ _ ?_
      by_cases hlbl : labels i = j
      · simp only [rawPatchUpdate, affinePatchUpdate, hlbl, ite_eq_right hx]; exact h0
      · rw [hm i hlbl]
        change (if x ∈ highTorusPatch d k (labels i) then
          slope (labels i) (marks' i) x * init.1 x + intercept (labels i) (marks' i) x else init.1 x) =
          (if x ∈ highTorusPatch d k (labels i) then
            slope (labels i) (marks' i) x * init'.1 x + intercept (labels i) (marks' i) x else init'.1 x)
        rw [h0]
  have hpI := affineRawHistory_density_interval (highTorusPatch d k) slope intercept response labels indices marks a b hlegal initial hi
  have hp'I := affineRawHistory_density_interval (highTorusPatch d k) slope intercept response labels indices marks' a b hlegal initial hi
  let K : ℝ := max |a| |b|
  have hbnd (q : Covariate d → ℝ) (hq : ∀ x, q x ∈ Icc a b) (x) : ‖q x‖ ≤ K := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [(hq x).1, neg_abs_le a, le_max_left |a| |b|],
      (hq x).2.trans ((le_abs_self b).trans (le_max_right _ _))⟩
  have hip : Integrable p (cubeVolume d) := (integrable_const K).mono' (hdMeas marks).aestronglyMeasurable (Eventually.of_forall (hbnd p hpI))
  have hip' : Integrable p' (cubeVolume d) := (integrable_const K).mono' (hdMeas marks').aestronglyMeasurable (Eventually.of_forall (hbnd p' hp'I))
  have hP := highTorusPatch_measurableSet d k j
  change |(∫ x, p x ∂cubeVolume d) - ∫ x, p' x ∂cubeVolume d| ≤ _
  rw [← integral_sub hip hip']
  have hdiff (x) : |p x - p' x| ≤ (highTorusPatch d k j).indicator (fun _ => b - a) x := by
    by_cases hx : x ∈ highTorusPatch d k j
    · rw [Set.indicator_of_mem hx]
      exact abs_le.mpr ⟨by linarith [(hpI x).1, (hpI x).2, (hp'I x).1, (hp'I x).2],
        by linarith [(hpI x).1, (hpI x).2, (hp'I x).1, (hp'I x).2]⟩
    · rw [Set.indicator_of_notMem hx, hout x hx, sub_self, abs_zero]
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hvol : (cubeVolume d).real (highTorusPatch d k j) ≤ (2 / (k : ℝ))^d := by
    simpa only [measureReal_def, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 / (k : ℝ))] using
      ENNReal.toReal_mono (by finiteness) (highTorusPatch_volume_le d k hk j)
  calc
    _ ≤ ∫ x, |p x - p' x| ∂cubeVolume d := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm fun x => p x - p' x
    _ ≤ ∫ x, (highTorusPatch d k j).indicator (fun _ => b - a) x ∂cubeVolume d :=
      integral_mono (hip.sub hip').abs ((integrable_const (b - a)).indicator hP) hdiff
    _ = (cubeVolume d).real (highTorusPatch d k j) * (b - a) := by rw [integral_indicator_const _ hP, smul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hvol (sub_nonneg.mpr hab)

theorem affinePatchFold_density_eq {J X E V I : Type*} [DecidableEq J]
    (patch : J → Set X) (slope offset : J → E → X → ℝ)
    (response : J → E → V → V) (labels : I → J) (marks : I → E)
    (indices : List I) (initial : (X → ℝ) × (J → V)) (x : X) :
    (indices.foldl (fun θ i => rawPatchUpdate (labels i) (patch (labels i))
      (slope (labels i) (marks i)) (offset (labels i) (marks i))
      (response (labels i) (marks i)) θ) initial).1 x =
      indices.foldl (fun v i =>
        (if x ∈ patch (labels i) then slope (labels i) (marks i) x else 1) * v +
        (if x ∈ patch (labels i) then offset (labels i) (marks i) x else 0)) (initial.1 x) := by
  induction indices generalizing initial with
  | nil => rfl
  | cons i indices ih =>
    simp only [List.foldl_cons]; rw [ih]
    by_cases hx : x ∈ patch (labels i) <;>
      simp only [rawPatchUpdate, affinePatchUpdate, hx, ite_true, ite_false, one_mul, add_zero]

theorem affinePatchFold_density_joint_measurable {J X E V : Type*} [DecidableEq J]
    [MeasurableSpace X] [MeasurableSpace E]
    (patch : J → Set X) (hpatch : ∀ j, MeasurableSet (patch j))
    (slope offset : J → E → X → ℝ)
    (hs : ∀ j, Measurable fun ex : E × X => slope j ex.1 ex.2)
    (ho : ∀ j, Measurable fun ex : E × X => offset j ex.1 ex.2)
    (response : J → E → V → V) (n : ℕ) (labels : Fin n → J) (indices : List (Fin n))
    (initial : (Fin n → E) → (X → ℝ) × (J → V))
    (hi : Measurable fun mx : (Fin n → E) × X => (initial mx.1).1 mx.2) :
    Measurable fun mx : (Fin n → E) × X =>
      (indices.foldl (fun θ i => rawPatchUpdate (labels i) (patch (labels i))
        (slope (labels i) (mx.1 i)) (offset (labels i) (mx.1 i))
        (response (labels i) (mx.1 i)) θ) (initial mx.1)).1 mx.2 := by
  induction indices generalizing initial with
  | nil => exact hi
  | cons i indices ih =>
    simp only [List.foldl_cons]
    refine ih (fun marks => rawPatchUpdate (labels i) (patch (labels i))
      (slope (labels i) (marks i)) (offset (labels i) (marks i))
      (response (labels i) (marks i)) (initial marks)) ?_
    change Measurable fun mx : (Fin n → E) × X =>
      if mx.2 ∈ patch (labels i) then slope (labels i) (mx.1 i) mx.2 *
        (initial mx.1).1 mx.2 + offset (labels i) (mx.1 i) mx.2 else (initial mx.1).1 mx.2
    have hcoord : Measurable fun mx : (Fin n → E) × X => (mx.1 i, mx.2) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
    exact Measurable.ite ((hpatch _).preimage measurable_snd)
      (((hs (labels i)).comp hcoord).mul hi |>.add ((ho (labels i)).comp hcoord)) hi

end RawDensityLocality

theorem packetSum_borelSpace {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B] : BorelSpace (A ⊕ B) := by
  constructor
  refine le_antisymm (fun s hs => ?_) (MeasurableSpace.generateFrom_le fun s hs =>
    measurableSet_sum_iff.mpr ⟨(hs.preimage continuous_inl).measurableSet,
      (hs.preimage continuous_inr).measurableSet⟩)
  have hsec := measurableSet_sum_iff.mp hs
  let : MeasurableSpace (A ⊕ B) := borel (A ⊕ B)
  let : BorelSpace (A ⊕ B) := ⟨rfl⟩
  rw [show s = Sum.inl '' (Sum.inl ⁻¹' s) ∪ Sum.inr '' (Sum.inr ⁻¹' s) by ext x; cases x <;> simp]
  exact (Topology.IsClosedEmbedding.inl.measurableEmbedding.measurableSet_image' hsec.1).union
    (Topology.IsClosedEmbedding.inr.measurableEmbedding.measurableSet_image' hsec.2)

def historyWordMarkedState {J E X : Type*} (update : J → E → X → X)
    (initial : X) (word : List J) (marks : Fin word.length → E) : X :=
  historyWordState (fun p : J × E => update p.1 p.2) initial
    (List.ofFn fun i => (word.get i, marks i))

private lemma historyFold_linear_extension_invariant {ι X : Type*} [PartialOrder ι]
    (dependent : ι → ι → Prop) (update : ι → X → X)
    (hcomp : ∀ x y, dependent x y → x ≤ y ∨ y ≤ x)
    (hcomm : ∀ x y, ¬ dependent x y → ∀ state, update y (update x state) = update x (update y state))
    {l l' : List ι} (hperm : l.Perm l')
    (hl : l.Pairwise fun x y => ¬ y ≤ x) (hl' : l'.Pairwise fun x y => ¬ y ≤ x) (init : X) :
    l.foldl (fun state x => update x state) init = l'.foldl (fun state x => update x state) init := by
  induction l' generalizing l init with
  | nil => obtain rfl := List.perm_nil.mp hperm; rfl
  | cons x xs ih =>
    obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp (hperm.mem_iff.mpr List.mem_cons_self)
    obtain ⟨_, _, hcross⟩ := List.pairwise_append.mp hl
    have hmove : ∀ y ∈ before, ∀ state, update x (update y state) = update y (update x state) := by
      intro y hy state
      have hxy : ¬ x ≤ y := hcross y hy x List.mem_cons_self
      have hyne : y ≠ x := fun h => hxy (h ▸ le_rfl)
      have hymem : y ∈ xs := by
        simpa only [List.mem_cons, hyne, false_or] using hperm.mem_iff.mp (List.mem_append_left _ hy)
      exact (hcomm x y (fun hd => (hcomp x y hd).elim hxy ((List.pairwise_cons.mp hl').1 y hymem)) state).symm
    have hfold : ∀ (bs : List ι), (∀ y ∈ bs, ∀ state, update x (update y state) = update y (update x state)) →
        ∀ state, update x (bs.foldl (fun s y => update y s) state) =
          bs.foldl (fun s y => update y s) (update x state) := by
      intro bs; induction bs with
      | nil => intro _ _; rfl
      | cons y ys ihy =>
        intro hm state; simp only [List.foldl_cons]
        rw [ihy (fun z hz => hm z (List.mem_cons_of_mem y hz)), hm y List.mem_cons_self]
    simp only [List.foldl_append, List.foldl_cons]; rw [hfold before hmove, ← List.foldl_append]
    exact ih ((List.perm_middle.symm.trans hperm).cons_inv)
      (hl.sublist (List.Sublist.append (List.Sublist.refl before) (List.Sublist.cons x (List.Sublist.refl after))))
      hl'.of_cons (update x init)

theorem historyHeapMarkEquiv_state {J E X : Type*} [MeasurableSpace E]
    (dependent : J → J → Prop)
    (hsymm : ∀ ⦃a b⦄, dependent a b → dependent b a)
    (update : J → E → X → X)
    (hcomm : ∀ j k, ¬ dependent j k → ∀ e f state,
      update k f (update j e state) = update j e (update k f state))
    {u v : List J} (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent)
    (he : ∀ x, wordHeapLabel (e x) = wordHeapLabel x)
    (initial : X) (marks : Fin u.length → E) :
    historyWordMarkedState update initial v (historyHeapMarkEquiv e marks) =
      historyWordMarkedState update initial u marks := by
  classical
  let l := List.ofFn fun i : Fin u.length => (⟨i⟩ : WordHeapPiece u dependent)
  let l' := List.ofFn fun i : Fin v.length => e.symm (⟨i⟩ : WordHeapPiece v dependent)
  have hp : l.Perm l' := (List.perm_ext_iff_of_nodup
    (List.nodup_ofFn.mpr fun _ _ h => congrArg WordHeapPiece.position h)
    (List.nodup_ofFn.mpr fun _ _ h => congrArg WordHeapPiece.position (e.symm.injective h))).mpr fun x =>
    ⟨fun _ => List.mem_ofFn.mpr ⟨(e x).position, by
        have hx : (⟨(e x).position⟩ : WordHeapPiece v dependent) = e x := by cases e x; rfl
        rw [hx, e.symm_apply_apply]⟩,
     fun _ => List.mem_ofFn.mpr ⟨x.position, by cases x; rfl⟩⟩
  have hl : l.Pairwise fun x y => ¬ y ≤ x := List.pairwise_iff_getElem.mpr fun i j hi hj hij hle => by
    have hh := wordHeap_reachable_position_le hle
    simp only [l, List.getElem_ofFn] at hh
    exact Nat.not_le_of_lt hij hh
  have hl' : l'.Pairwise fun x y => ¬ y ≤ x := List.pairwise_iff_getElem.mpr fun i j hi hj hij hle => by
    have hh := wordHeap_reachable_position_le (e.monotone hle)
    simp only [l', List.getElem_ofFn, OrderIso.apply_symm_apply] at hh
    exact Nat.not_le_of_lt hij hh
  have hwf {w : List J} (m₀ : Fin w.length → E) :
      historyWordMarkedState update initial w m₀ =
        (List.ofFn fun i : Fin w.length => (⟨i⟩ : WordHeapPiece w dependent)).foldl
          (fun state x => update (wordHeapLabel x) (m₀ x.position) state) initial := by
    unfold historyWordMarkedState historyWordState
    rw [show (List.ofFn fun i : Fin w.length => (w.get i, m₀ i)) =
      (List.ofFn fun i : Fin w.length => (⟨i⟩ : WordHeapPiece w dependent)).map
        fun x => (wordHeapLabel x, m₀ x.position) by rw [List.map_ofFn]; rfl, List.foldl_map]
  have hfold := historyFold_linear_extension_invariant
    (fun x y : WordHeapPiece u dependent => dependent (wordHeapLabel x) (wordHeapLabel y))
    (fun x state => update (wordHeapLabel x) (marks x.position) state)
    (fun _ _ => wordHeap_dependent_comparable hsymm)
    (fun _ _ h state => hcomm _ _ h _ _ state) hp hl hl' initial
  rw [hwf marks, hfold, hwf (historyHeapMarkEquiv e marks),
    show l' = (List.ofFn fun i : Fin v.length => (⟨i⟩ : WordHeapPiece v dependent)).map e.symm by
      rw [List.map_ofFn]; rfl, List.foldl_map]
  congr 1; funext state x
  have hlabel := he (e.symm x)
  have hmark := historyHeapMarkEquiv_position e marks (e.symm x)
  simp only [OrderIso.apply_symm_apply] at hlabel hmark
  simp only [hlabel, hmark]

section BoundedDiffMGF
variable {E : Type*} [MeasurableSpace E] [Nonempty E]

lemma exp_integral_le_of_oscillation (π : Measure E) [IsProbabilityMeasure π]
    (X : E → ℝ) (hX : Measurable X) (R c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ e, |X e| ≤ R) (hosc : ∀ e f, |X e - X f| ≤ c) (u : ℝ) :
    (∫ e, Real.exp (u * X e) ∂π) ≤
      Real.exp (u * ∫ e, X e ∂π) * Real.exp (u ^ 2 * c ^ 2 / 8) := by
  let S := Set.range X
  have hne : S.Nonempty := Set.range_nonempty X
  have hbelow : BddBelow S := ⟨-R, by rintro _ ⟨e, rfl⟩; exact (abs_le.1 (hbound e)).1⟩
  have habove : BddAbove S := ⟨R, by rintro _ ⟨e, rfl⟩; exact (abs_le.1 (hbound e)).2⟩
  have hrange : sSup S - sInf S ≤ c := by
    have hh : sSup S ≤ sInf S + c := csSup_le hne <| by
      rintro _ ⟨e, rfl⟩
      have hl : X e - c ≤ sInf S := le_csInf hne <| by
        rintro _ ⟨f, rfl⟩; linarith [(abs_le.1 (hosc e f)).2]
      linarith
    linarith
  have horder : 0 ≤ sSup S - sInf S := sub_nonneg.2 (csInf_le_csSup hne hbelow habove)
  have hsg := hasSubgaussianMGF_of_mem_Icc (μ := π) (X := X) (a := sInf S) (b := sSup S)
    hX.aemeasurable (Eventually.of_forall fun e => ⟨csInf_le hbelow ⟨e, rfl⟩, le_csSup habove ⟨e, rfl⟩⟩)
  have hcent : (∫ e, Real.exp (u * (X e - ∫ f, X f ∂π)) ∂π) ≤ Real.exp (u ^ 2 * c ^ 2 / 8) := by
    refine (hsg.mgf_le u).trans (Real.exp_le_exp.2 ?_)
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat, abs_of_nonneg horder]
    nlinarith [mul_le_mul_of_nonneg_right ((sq_le_sq₀ horder hc).2 hrange) (sq_nonneg u)]
  rw [show (fun e => Real.exp (u * X e)) =
    fun e => Real.exp (u * ∫ f, X f ∂π) * Real.exp (u * (X e - ∫ f, X f ∂π)) from
      funext fun _ => by rw [← Real.exp_add]; congr 1; ring, integral_const_mul]
  exact mul_le_mul_of_nonneg_left hcent (Real.exp_pos _).le

theorem product_centered_mgf_le (n : ℕ) (π : Fin n → Measure E)
    [∀ i, IsProbabilityMeasure (π i)]
    (F : (Fin n → E) → ℝ) (hF : Measurable F) (R c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ x, |F x| ≤ R)
    (hosc : ∀ i x y, |F (Function.update x i y) - F x| ≤ c) (u : ℝ) :
    (∫ x, Real.exp (u * (F x - ∫ y, F y ∂Measure.pi π)) ∂Measure.pi π) ≤
      Real.exp ((n : ℝ) * u ^ 2 * c ^ 2 / 8) := by
  have hexp : ∀ (m : ℕ) (πm : Fin m → Measure E) [∀ i, IsProbabilityMeasure (πm i)]
      (Fm : (Fin m → E) → ℝ), Measurable Fm → (∀ x, |Fm x| ≤ R) →
      (∀ i x y, |Fm (Function.update x i y) - Fm x| ≤ c) →
      (∫ x, Real.exp (u * Fm x) ∂Measure.pi πm) ≤
        Real.exp (u * ∫ x, Fm x ∂Measure.pi πm) * Real.exp ((m : ℝ) * u ^ 2 * c ^ 2 / 8) := by
    intro m; induction m with
    | zero =>
      intro πm _ Fm _ _ _
      rw [show Fm = fun _ => Fm Fin.elim0 from funext fun _ => congrArg Fm (Subsingleton.elim _ _)]
      simp
    | succ m ih =>
      intro πm _ Fm hFm hbFm hoFm
      let ν := πm (Fin.last m)
      let μ := Measure.pi fun i : Fin m => πm i.castSucc
      let e := historyFiniteMarkAppendEquiv m (E := E)
      have hsnoc (fresh : E) (marks : Fin m → E) : e (fresh, marks) = Fin.snoc marks fresh :=
        funext fun i => Fin.lastCases (by rw [historyFiniteMarkAppendEquiv_last, Fin.snoc_last])
          (fun _ => by rw [historyFiniteMarkAppendEquiv_old, Fin.snoc_castSucc]) i
      have hp : MeasurePreserving e (ν.prod μ) (Measure.pi πm) := by
        simpa only [e, historyFiniteMarkAppendEquiv, Fin.succAbove_last_apply] using
          (measurePreserving_piFinSuccAbove πm (Fin.last m)).symm _
      let H := fun p : E × (Fin m → E) => Fm (e p)
      have hH : Measurable H := hFm.comp e.measurable
      have hHi : Integrable H (ν.prod μ) := Integrable.of_bound hH.aestronglyMeasurable R
        (Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hbFm (e p))
      let G := fun x : Fin m → E => ∫ y, H (y, x) ∂ν
      have hG : Measurable G := hH.stronglyMeasurable.integral_prod_left'.measurable
      have hXi (x) : Integrable (fun y => H (y, x)) ν :=
        Integrable.of_bound (hH.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable R
          (Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs, H] using hbFm (e (y, x)))
      have hGb (x) : |G x| ≤ R := by
        simpa [G, Real.norm_eq_abs] using norm_integral_le_of_norm_le_const (μ := ν) (f := fun y => H (y, x)) (C := R)
          (Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs, H] using hbFm (e (y, x)))
      have hGo (i x y) : |G (Function.update x i y) - G x| ≤ c := by
        change |(∫ z, H (z, Function.update x i y) ∂ν) - ∫ z, H (z, x) ∂ν| ≤ c
        rw [← integral_sub (hXi _) (hXi _)]
        have hb : ∀ᵐ z ∂ν, ‖H (z, Function.update x i y) - H (z, x)‖ ≤ c :=
          Eventually.of_forall fun z => by
            simpa only [H, hsnoc, Fin.snoc_update, Real.norm_eq_abs] using hoFm i.castSucc (Fin.snoc x z) y
        simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const hb
      have hpoint (x) : (∫ y, Real.exp (u * H (y, x)) ∂ν) ≤ Real.exp (u * G x) * Real.exp (u ^ 2 * c ^ 2 / 8) :=
        exp_integral_le_of_oscillation ν (fun y => H (y, x))
          (hH.comp (measurable_id.prodMk measurable_const)) R c hc (fun y => hbFm (e (y, x)))
          (fun y z => by simpa only [H, hsnoc, Fin.update_snoc_last] using hoFm (Fin.last m) (Fin.snoc x z) y) u
      have hEi : Integrable (fun p => Real.exp (u * H p)) (ν.prod μ) :=
        Integrable.of_bound (Real.measurable_exp.comp (measurable_const.mul hH)).aestronglyMeasurable (Real.exp (|u| * R))
          (Eventually.of_forall fun p => by
            change ‖Real.exp (u * H p)‖ ≤ _; rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            exact Real.exp_le_exp.2 ((le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hbFm (e p)) (abs_nonneg u))))
      have hEGi : Integrable (fun x => Real.exp (u * G x)) μ :=
        Integrable.of_bound (Real.measurable_exp.comp (measurable_const.mul hG)).aestronglyMeasurable (Real.exp (|u| * R))
          (Eventually.of_forall fun x => by
            change ‖Real.exp (u * G x)‖ ≤ _; rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            exact Real.exp_le_exp.2 ((le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hGb x) (abs_nonneg u))))
      rw [← hp.integral_comp' fun x => Real.exp (u * Fm x), integral_prod_symm _ hEi,
        ← hp.integral_comp' Fm, integral_prod_symm H hHi]
      calc
        _ ≤ ∫ x, Real.exp (u * G x) * Real.exp (u ^ 2 * c ^ 2 / 8) ∂μ :=
          integral_mono hEi.integral_prod_right (hEGi.mul_const _) hpoint
        _ = (∫ x, Real.exp (u * G x) ∂μ) * Real.exp (u ^ 2 * c ^ 2 / 8) := integral_mul_const _ _
        _ ≤ (Real.exp (u * ∫ x, G x ∂μ) * Real.exp ((m : ℝ) * u ^ 2 * c ^ 2 / 8)) *
            Real.exp (u ^ 2 * c ^ 2 / 8) :=
          mul_le_mul_of_nonneg_right (ih (fun i : Fin m => πm i.castSucc) G hG hGb hGo) (Real.exp_pos _).le
        _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; push_cast; ring
  let m := ∫ y, F y ∂Measure.pi π
  change (∫ x, Real.exp (u * (F x - m)) ∂Measure.pi π) ≤ _
  rw [show (fun x => Real.exp (u * (F x - m))) = fun x => Real.exp (-u * m) * Real.exp (u * F x) from
    funext fun _ => by rw [← Real.exp_add]; congr 1; ring, integral_const_mul]
  exact (mul_le_mul_of_nonneg_left (hexp n π F hF hbound hosc) (Real.exp_pos _).le).trans_eq
    (by rw [← mul_assoc, ← Real.exp_add]; dsimp [m]; rw [show -u * ∫ y, F y ∂Measure.pi π + u * ∫ x, F x ∂Measure.pi π = 0 by ring, Real.exp_zero, one_mul])

end BoundedDiffMGF

section ExpectationAndObservables
variable {J : Type*} [Fintype J] [LinearOrder J]

lemma historyMarkedDensity_lipschitzOn (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (ρ T B : ℝ) (hρ : 0 < ρ) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    (a : E → ℝ) (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)) (h : HistoryMarked dependent E) :
    LipschitzOnWith ⟨ρ⁻¹ * (Fintype.card J : ℝ) * B * (3 / 2 : ℝ) ^ Fintype.card J, by positivity⟩
      (fun t => historyMarkedDensity dependent ρ t a h) (Icc 0 T) := by
  refine (convex_Icc (0 : ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun u _ => (historyMarkedDensity_hasDerivAt dependent ρ u a h).hasDerivWithinAt) fun u hu => NNReal.coe_le_coe.1 ?_
  change ‖historyMarkedDensityDerivative dependent ρ u a h‖ ≤ _
  rw [Real.norm_eq_abs]
  exact historyMarkedDensityDerivative_bound dependent hrefl hsymm Δ hlabels ρ u B hρ hu.1 hB a habound
    ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hB) hρ.le).trans hsmall) h

theorem historyMarkedExpectation_absolutelyContinuous (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (ρ T B : ℝ) (hρ : 0 < ρ) (hT : 0 ≤ T) (hB : 0 ≤ B)
    {E : Type*} [MeasurableSpace E] (μ : Measure (HistoryMarked dependent E)) [IsProbabilityMeasure μ]
    (a : E → ℝ) (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F : HistoryMarked dependent E → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M) :
    AbsolutelyContinuousOnInterval (historyMarkedExpectation dependent ρ μ a F) 0 T := by
  let D : ℝ := ρ⁻¹ * (Fintype.card J : ℝ) * B * (3 / 2 : ℝ) ^ Fintype.card J
  have hi (u : ℝ) (hu : u ∈ Icc 0 T) : Integrable (fun h => F h * historyMarkedDensity dependent ρ u a h) μ :=
    Integrable.of_bound (hF.mul (historyMarkedDensity_measurable dependent ρ u a ha)).aestronglyMeasurable
      (M * (3 / 2 : ℝ) ^ Fintype.card J) <| Eventually.of_forall fun h => by
        change ‖F h * historyMarkedDensity dependent ρ u a h‖ ≤ _
        rw [Real.norm_eq_abs, abs_mul]
        have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels ρ u B hρ hu.1 hB a habound
          ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hB) hρ.le).trans hsmall) h
        have hp : 0 ≤ historyMarkedDensity dependent ρ u a h :=
          (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
        rw [abs_of_nonneg hp]
        exact mul_le_mul (hFbound h) hb.2 hp hM
  have hl : LipschitzOnWith ⟨M * D, by dsimp [D]; positivity⟩
      (historyMarkedExpectation dependent ρ μ a F) (Icc 0 T) := by
    refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
    rw [Real.dist_eq, historyMarkedExpectation, historyMarkedExpectation, ← integral_sub (hi u hu) (hi v hv)]
    change ‖∫ h, F h * historyMarkedDensity dependent ρ u a h - F h * historyMarkedDensity dependent ρ v a h ∂μ‖ ≤
      M * D * dist u v
    have hb : ∀ᵐ h ∂μ, ‖F h * historyMarkedDensity dependent ρ u a h - F h * historyMarkedDensity dependent ρ v a h‖ ≤ M * D * dist u v :=
      Eventually.of_forall fun h => by
        rw [← mul_sub, norm_mul, Real.norm_eq_abs]
        have hl0 := (historyMarkedDensity_lipschitzOn dependent hrefl hsymm Δ hlabels ρ T B hρ hB a habound hsmall h).dist_le_mul u hu v hv
        rw [dist_eq_norm] at hl0
        change ‖historyMarkedDensity dependent ρ u a h - historyMarkedDensity dependent ρ v a h‖ ≤ D * dist u v at hl0
        exact (mul_le_mul_of_nonneg_right (hFbound h) (norm_nonneg _)).trans
          (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hl0 hM)
    simpa using norm_integral_le_of_norm_le_const hb
  rw [← uIcc_of_le hT] at hl
  exact hl.absolutelyContinuousOnInterval

theorem historyMarkedPrior_variable_observable_lipschitz (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T B : ℝ) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (G : ℝ → HistoryMarked dependent E → ℝ) (hGM : ∀ u, Measurable (G u))
    (M : ℝ) (hM : 0 ≤ M) (hGb : ∀ u ∈ Icc 0 T, ∀ h, |G u h| ≤ M)
    (K : NNReal) (hGlip : ∀ h, LipschitzOnWith K (fun u => G u h) (Icc 0 T)) :
    LipschitzOnWith
      ⟨(K : ℝ) * (3 / 2 : ℝ) ^ Fintype.card J +
        M * ((historyReferenceRho Δ)⁻¹ * (Fintype.card J : ℝ) * B * (3 / 2 : ℝ) ^ Fintype.card J),
        by have hρ := historyReferenceRho_pos Δ; positivity⟩
      (fun u => ∫ h, G u h ∂historyMarkedPrior dependent Δ u π a) (Icc 0 T) := by
  let μ := historyMarkedReference dependent Δ π
  let _ : IsProbabilityMeasure μ := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
  let ρ := historyReferenceRho Δ
  let C : ℝ := (3 / 2 : ℝ) ^ Fintype.card J
  let D : ℝ := ρ⁻¹ * (Fintype.card J : ℝ) * B * C
  have hρ : 0 < ρ := historyReferenceRho_pos Δ
  have hs (u : ℝ) (hu : u ∈ Icc 0 T) : u * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hB) hρ.le).trans hsmall
  have hφ (u : ℝ) (hu : u ∈ Icc 0 T) (h : HistoryMarked dependent E) :
      ‖historyMarkedDensity dependent ρ u a h‖ ≤ C := by
    have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels ρ u B hρ hu.1 hB a habound (hs u hu) h
    rw [Real.norm_eq_abs, abs_of_nonneg ((by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1)]
    exact hb.2
  let H : ℝ → HistoryMarked dependent E → ℝ := fun u h => G u h * historyMarkedDensity dependent ρ u a h
  have hi (u : ℝ) (hu : u ∈ Icc 0 T) : Integrable (H u) μ :=
    Integrable.of_bound ((hGM u).mul (historyMarkedDensity_measurable dependent ρ u a ha)).aestronglyMeasurable (M * C) <|
      Eventually.of_forall fun h => by
        change ‖G u h * historyMarkedDensity dependent ρ u a h‖ ≤ _
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul (hGb u hu h) (hφ u hu h) (norm_nonneg _) hM
  refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
  rw [historyMarkedPrior_integral_eq_expectation dependent hrefl hsymm Δ hlabels u B hu.1 hB π a ha habound (hs u hu),
    historyMarkedPrior_integral_eq_expectation dependent hrefl hsymm Δ hlabels v B hv.1 hB π a ha habound (hs v hv)]
  change dist (∫ h, H u h ∂μ) (∫ h, H v h ∂μ) ≤ ((K : ℝ) * C + M * D) * dist u v
  rw [dist_eq_norm, ← integral_sub (hi u hu) (hi v hv)]
  have hb : ∀ᵐ h ∂μ, ‖H u h - H v h‖ ≤ ((K : ℝ) * C + M * D) * dist u v :=
    Eventually.of_forall fun h => by
      have hGdiff := (hGlip h).dist_le_mul u hu v hv; rw [dist_eq_norm] at hGdiff
      have hφdiff := (historyMarkedDensity_lipschitzOn dependent hrefl hsymm Δ hlabels ρ T B hρ hB a habound hsmall h).dist_le_mul u hu v hv
      rw [dist_eq_norm] at hφdiff
      rw [show H u h - H v h = (G u h - G v h) * historyMarkedDensity dependent ρ u a h +
        G v h * (historyMarkedDensity dependent ρ u a h - historyMarkedDensity dependent ρ v a h) by dsimp [H]; ring]
      calc
        _ ≤ ‖(G u h - G v h) * historyMarkedDensity dependent ρ u a h‖ +
            ‖G v h * (historyMarkedDensity dependent ρ u a h - historyMarkedDensity dependent ρ v a h)‖ := norm_add_le _ _
        _ ≤ ((K : ℝ) * dist u v) * C + M * (D * dist u v) := by
          rw [norm_mul, norm_mul]
          exact add_le_add (mul_le_mul hGdiff (hφ u hu h) (norm_nonneg _) (by positivity))
            (mul_le_mul (by simpa only [Real.norm_eq_abs] using hGb v hv h) hφdiff (norm_nonneg _) hM)
        _ = _ := by ring
  simpa using norm_integral_le_of_norm_le_const hb

end ExpectationAndObservables

def highRawSampleVarianceDerivative {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Covariate d → ℝ) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  (∏ i, p (z.1 i)) * ∑ i, (∏ j ∈ Finset.univ.erase i,
    ternaryMass a (F (z.1 j)) V (z.2 j)) * ternaryVarianceDerivative a (z.2 i)

theorem highRawSampleLikelihood_hasDerivAt_path {d : ℕ} (n : ℕ) (a v η t : ℝ)
    (p F : Covariate d → ℝ) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    HasDerivAt (fun u => highRawSampleLikelihood n a (v - η ^ 2 * u) p F z)
      (-η ^ 2 * highRawSampleVarianceDerivative n a (v - η ^ 2 * t) p F z) t := by
  have hvar : HasDerivAt (fun W => highRawSampleLikelihood n a W p F z)
      (highRawSampleVarianceDerivative n a (v - η ^ 2 * t) p F z) (v - η ^ 2 * t) := by
    simpa only [highRawSampleLikelihood, highRawSampleVarianceDerivative,
      Finset.prod_mul_distrib, smul_eq_mul] using
      (HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin n)))
        fun i _ => ternary_hasDerivAt_variance a (F (z.1 i)) (v - η ^ 2 * t) (z.2 i)).const_mul (∏ i, p (z.1 i))
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, zero_sub, mul_one, mul_comm] using
    hvar.comp t ((hasDerivAt_const t v).sub ((hasDerivAt_id t).const_mul (η ^ 2)))

theorem highRawSampleLikelihood_abs_le {d : ℕ} (n : ℕ) (a V P : ℝ) (hP : 0 ≤ P)
    (p F : Covariate d → ℝ) (hp : ∀ x, |p x| ≤ P) (ha : a ≠ 0)
    (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    |highRawSampleLikelihood n a V p F z| ≤ P ^ n := by
  unfold highRawSampleLikelihood; rw [Finset.abs_prod]
  refine (Finset.prod_le_prod₀ (g := fun _ => P) (fun _ _ => abs_nonneg _) fun i _ => ?_).trans_eq (by simp)
  rw [abs_mul, abs_of_nonneg (hq (z.1 i) (z.2 i))]
  exact (mul_le_mul (hp _) (ternary_mass_le_one a _ V ha (hq _) _) (hq _ _) hP).trans_eq (mul_one _)

theorem highRawSampleVarianceDerivative_abs_le {d : ℕ} (n : ℕ) (a V P : ℝ)
    (ha : 0 < a) (hP : 0 ≤ P) (p F : Covariate d → ℝ)
    (hp : ∀ x, |p x| ≤ P) (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    |highRawSampleVarianceDerivative n a V p F z| ≤ P ^ n * ((n : ℝ) / a ^ 2) := by
  have hpp : |∏ i : Fin n, p (z.1 i)| ≤ P ^ n := by
    rw [Finset.abs_prod]
    simpa using Finset.prod_le_prod₀ (s := Finset.univ) (f := fun i => |p (z.1 i)|) (g := fun _ => P)
      (fun _ _ => abs_nonneg _) fun i _ => hp (z.1 i)
  have hs : |∑ i : Fin n, (∏ j ∈ Finset.univ.erase i,
      ternaryMass a (F (z.1 j)) V (z.2 j)) * ternaryVarianceDerivative a (z.2 i)| ≤ (n : ℝ) / a ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun i _ => ?_ : _ ≤ ∑ _i : Fin n, 1 / a ^ 2).trans_eq (by simp [div_eq_mul_inv]))
    rw [abs_mul, Finset.abs_prod]
    exact (mul_le_mul (Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun j _ => by
        rw [abs_of_nonneg (hq (z.1 j) (z.2 j))]; exact ternary_mass_le_one a _ V ha.ne' (hq _) _)
      (ternary_variance_derivative_abs_bound a ha (z.2 i))
      (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  rw [highRawSampleVarianceDerivative, abs_mul]
  exact mul_le_mul hpp hs (abs_nonneg _) (pow_nonneg hP n)

theorem highRawSampleVarianceDerivative_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) :
    Measurable fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highRawSampleVarianceDerivative n a V (p z.1) (F z.1) z.2 := by
  have hx (i : Fin n) : Measurable fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) => (z.1, z.2.1 i) :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  have hy (i : Fin n) : Measurable fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) => z.2.2 i :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  exact (Finset.measurable_prod _ fun i _ => hp.comp (hx i)).mul
    (Finset.measurable_sum _ fun i _ =>
      (Finset.measurable_prod _ fun j _ =>
        (ternaryMass_joint_measurable a V (Function.uncurry F) hF).comp ((hx j).prodMk (hy j))).mul
      ((measurable_of_countable (ternaryVarianceDerivative a)).comp (hy i)))

def highRawObservable {d : ℕ} (n : ℕ) (a V : ℝ) (p F : Covariate d → ℝ)
    (H : (Fin n → Observation d) → ℝ) : ℝ :=
  ∫ z, H (encodeDesignResponse a z) * highRawSampleLikelihood n a V p F z
    ∂highSampleReference d n

def highRawObservableVarianceDerivative {d : ℕ} (n : ℕ) (a V : ℝ) (p F : Covariate d → ℝ)
    (H : (Fin n → Observation d) → ℝ) : ℝ :=
  ∫ z, H (encodeDesignResponse a z) * highRawSampleVarianceDerivative n a V p F z
    ∂highSampleReference d n

theorem highRawObservable_measurable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (H : (Fin n → Observation d) → ℝ)
    (hH : Measurable H) : Measurable fun ω => highRawObservable n a V (p ω) (F ω) H := by
  have h : Measurable fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      H (encodeDesignResponse a z.2) * highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 :=
    ((hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd).mul
      (highRawSampleLikelihood_joint_measurable n a V p F hp hF)
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem highRawObservableVarianceDerivative_measurable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (n : ℕ) (a V : ℝ) (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (H : (Fin n → Observation d) → ℝ)
    (hH : Measurable H) :
    Measurable fun ω => highRawObservableVarianceDerivative n a V (p ω) (F ω) H := by
  have h : Measurable fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      H (encodeDesignResponse a z.2) * highRawSampleVarianceDerivative n a V (p z.1) (F z.1) z.2 :=
    ((hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd).mul
      (highRawSampleVarianceDerivative_joint_measurable n a V p F hp hF)
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem highRawObservable_abs_le {d : ℕ} (n : ℕ) (a V P B : ℝ) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (p F : Covariate d → ℝ) (hp : ∀ x, |p x| ≤ P) (ha : a ≠ 0)
    (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (H : (Fin n → Observation d) → ℝ) (hHb : ∀ z, |H z| ≤ B) :
    |highRawObservable n a V p F H| ≤ B * P ^ n * (highSampleReference d n).real Set.univ := by
  rw [highRawObservable, ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le_const <| Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hHb _) (highRawSampleLikelihood_abs_le n a V P hP p F hp ha hq z) (abs_nonneg _) hB

theorem highRawObservableVarianceDerivative_abs_le {d : ℕ} (n : ℕ) (a V P B : ℝ)
    (ha : 0 < a) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (p F : Covariate d → ℝ) (hp : ∀ x, |p x| ≤ P)
    (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (H : (Fin n → Observation d) → ℝ) (hHb : ∀ z, |H z| ≤ B) :
    |highRawObservableVarianceDerivative n a V p F H| ≤
      B * (P ^ n * ((n : ℝ) / a ^ 2)) * (highSampleReference d n).real Set.univ := by
  rw [highRawObservableVarianceDerivative, ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le_const <| Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hHb _) (highRawSampleVarianceDerivative_abs_le n a V P ha hP p F hp hq z) (abs_nonneg _) hB

theorem massPowerTilt_highReal_observable_mean {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (a V : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) (ha : a ≠ 0)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hHb : ∀ z, |H z| ≤ B) :
    (∫ ω, ∫ z, H z ∂highRealSampleKernel n a V p F hp hF ω
      ∂massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n) =
      (massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ ω, highRawObservable n a V (p ω) (F ω) H ∂ν := by
  let m : Ω → ℝ := fun ω => highRawDensityMass (p ω)
  have hm : Measurable m := highRawDensityMass_joint_measurable p hp
  have hbound (ω : Ω) : aRaw ≤ m ω ∧ m ω ≤ bRaw :=
    highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw (Eventually.of_forall (hraw ω))
  let _ := massPowerTilt_isProbability ν m hm n aRaw bRaw haRaw hbound
  let _ := highSampleIndexKernel_markov n a V p F hp hF aRaw bRaw haRaw hraw ha hq
  have hM : Measurable fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      H (encodeDesignResponse a z.2) := (hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd
  have hInt : Integrable (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      H (encodeDesignResponse a z.2))
      ((massPowerTilt ν m n).compProd (highSampleIndexKernel n a V p F hp hF)) :=
    Integrable.of_bound hM.aestronglyMeasurable B
      (Eventually.of_forall fun _ => by simpa only [Real.norm_eq_abs] using hHb _)
  have hpabs (ω : Ω) (x : Covariate d) : |p ω x| ≤ |bRaw| := by
    rw [abs_of_nonneg (haRaw.le.trans (hraw ω x).1)]
    exact (hraw ω x).2.trans (le_abs_self _)
  have hIntRaw : Integrable (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 * H (encodeDesignResponse a z.2))
      (ν.prod (highSampleReference d n)) :=
    Integrable.of_bound ((highRawSampleLikelihood_joint_measurable n a V p F hp hF).mul hM).aestronglyMeasurable
      (|bRaw| ^ n * B) <| Eventually.of_forall fun z => by
        change ‖highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 * H (encodeDesignResponse a z.2)‖ ≤ _
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (highRawSampleLikelihood_abs_le n a V |bRaw| (abs_nonneg _) (p z.1) (F z.1)
          (hpabs z.1) ha (hq z.1) z.2) (hHb _) (abs_nonneg _) (pow_nonneg (abs_nonneg _) n)
  have he := massPowerTilt_highSample_integral ν n a V p F hp hF aRaw bRaw haRaw hraw hq
    fun z => H (encodeDesignResponse a z.2)
  rw [Measure.integral_compProd hInt, MeasureTheory.integral_prod _ hIntRaw] at he
  convert he using 1
  · refine integral_congr_ae <| Eventually.of_forall fun _ => ?_
    dsimp only
    rw [highRealSampleKernel_apply,
      integral_map_of_stronglyMeasurable (encodeDesignResponse_measurable a) hH.stronglyMeasurable]
  · congr 1
    exact integral_congr_ae <| Eventually.of_forall fun _ =>
      integral_congr_ae <| Eventually.of_forall fun _ => mul_comm _ _

theorem highRawObservable_hasDerivAt_path {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (n : ℕ) (a v η t T P B : ℝ)
    (ha : 0 < a) (ht : 0 < t) (htT : t < T) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (hpb : ∀ ω x, |p ω x| ≤ P)
    (hq : ∀ u ∈ Ioo 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H)
    (hHb : ∀ z, |H z| ≤ B) (ω : Ω) :
    HasDerivAt (fun u => highRawObservable n a (v - η ^ 2 * u) (p ω) (F ω) H)
      (-η ^ 2 * highRawObservableVarianceDerivative n a (v - η ^ 2 * t) (p ω) (F ω) H) t := by
  let L : ℝ → ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ := fun u z =>
    H (encodeDesignResponse a z) * highRawSampleLikelihood n a (v - η ^ 2 * u) (p ω) (F ω) z
  let L' : ℝ → ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ := fun u z =>
    H (encodeDesignResponse a z) * (-η ^ 2 * highRawSampleVarianceDerivative n a (v - η ^ 2 * u) (p ω) (F ω) z)
  have hLM (u : ℝ) : Measurable (L u) := by
    have hj : Measurable (Function.uncurry fun ω z =>
        highRawSampleLikelihood n a (v - η ^ 2 * u) (p ω) (F ω) z) :=
      highRawSampleLikelihood_joint_measurable n a (v - η ^ 2 * u) p F hp hF
    exact (hH.comp (encodeDesignResponse_measurable a)).mul hj.of_uncurry_left
  have hL'M : Measurable (L' t) := by
    have hj : Measurable (Function.uncurry fun ω z =>
        highRawSampleVarianceDerivative n a (v - η ^ 2 * t) (p ω) (F ω) z) :=
      highRawSampleVarianceDerivative_joint_measurable n a (v - η ^ 2 * t) p F hp hF
    exact (hH.comp (encodeDesignResponse_measurable a)).mul (hj.of_uncurry_left.const_mul (-η ^ 2))
  have hi : Integrable (L t) (highSampleReference d n) :=
    Integrable.of_bound (hLM t).aestronglyMeasurable (B * P ^ n) <| Eventually.of_forall fun z => by
      change ‖H (encodeDesignResponse a z) * highRawSampleLikelihood n a (v - η ^ 2 * t) (p ω) (F ω) z‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hHb _) (highRawSampleLikelihood_abs_le n a (v - η ^ 2 * t) P
        hP (p ω) (F ω) (hpb ω) ha.ne' (hq t ⟨ht, htT⟩ ω) z) (abs_nonneg _) hB
  have hb (u : ℝ) (hu : u ∈ Ioo 0 T) (z) :
      ‖L' u z‖ ≤ B * (η ^ 2 * (P ^ n * ((n : ℝ) / a ^ 2))) := by
    change ‖H (encodeDesignResponse a z) * (-η ^ 2 *
      highRawSampleVarianceDerivative n a (v - η ^ 2 * u) (p ω) (F ω) z)‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg η)]
    exact mul_le_mul (hHb _) (mul_le_mul_of_nonneg_left
      (highRawSampleVarianceDerivative_abs_le n a (v - η ^ 2 * u) P ha hP
        (p ω) (F ω) (hpb ω) (hq u hu ω) z) (sq_nonneg η)) (by positivity) hB
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := highSampleReference d n) (F := L) (F' := L')
    (bound := fun _ => B * (η ^ 2 * (P ^ n * ((n : ℝ) / a ^ 2))))
    (s := Ioo 0 T) (Ioo_mem_nhds ht htT)
    (Eventually.of_forall fun u => (hLM u).aestronglyMeasurable) hi
    hL'M.aestronglyMeasurable (Eventually.of_forall fun z u hu => hb u hu z)
    (integrable_const _)
    (Eventually.of_forall fun z u _ =>
      (highRawSampleLikelihood_hasDerivAt_path n a v η u (p ω) (F ω) z).const_mul
        (H (encodeDesignResponse a z)))).2
  change HasDerivAt (fun u => ∫ z, L u z ∂highSampleReference d n) _ t
  refine hd.congr_deriv ?_
  change (∫ z, L' t z ∂highSampleReference d n) =
    -η ^ 2 * ∫ z, H (encodeDesignResponse a z) *
      highRawSampleVarianceDerivative n a (v - η ^ 2 * t) (p ω) (F ω) z ∂highSampleReference d n
  rw [← integral_const_mul]
  exact integral_congr_ae <| Eventually.of_forall fun _ => by dsimp [L']; ring

end RowUnionHistoryAndObservables

-- ============================================================================
-- 4. Poisson Cell Field, Gaussian Hyperplane Geometry, and Bounded Field
-- ============================================================================

section PoissonHyperplaneField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

lemma even_cells_two_disjoint_pairs {I J : Type*} [DecidableEq I] [DecidableEq J]
    (s : Finset J) (p : J → I) (hs : 4 ≤ s.card)
    (h : ∀ i, Even ((s.filter fun j => p j = i).card)) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ∃ e ∈ s,
      b ≠ a ∧ c ≠ a ∧ c ≠ b ∧ e ≠ a ∧ e ≠ b ∧ e ≠ c ∧
        p b = p a ∧ p e = p c := by
  have hpart {u : Finset J} (hu : ∀ i, Even ((u.filter fun j => p j = i).card))
      {x : J} (hx : x ∈ u) : ∃ y ∈ u, y ≠ x ∧ p y = p x := by
    let f := u.filter fun j => p j = p x
    have hxf : x ∈ f := by simp [f, hx]
    have hpos : 0 < f.card := Finset.card_pos.mpr ⟨x, hxf⟩
    have he : Even f.card := hu (p x)
    obtain ⟨k, hk⟩ := he
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hxf]; omega : 0 < (f.erase x).card)
    obtain ⟨hyx, hyf⟩ := Finset.mem_erase.mp hy
    exact ⟨y, (Finset.mem_filter.mp hyf).1, hyx, (Finset.mem_filter.mp hyf).2⟩
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  obtain ⟨b, hb, hab, hpab⟩ := hpart h ha
  let t := (s.erase a).erase b
  have hbe : b ∈ s.erase a := by simp [hab, hb]
  have ht : 2 ≤ t.card := by simp only [t, Finset.card_erase_of_mem hbe, Finset.card_erase_of_mem ha]; omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < t.card)
  have heven (i : I) : Even ((t.filter fun j => p j = i).card) := by
    dsimp [t]; rw [Finset.filter_erase, Finset.filter_erase]
    by_cases hpa : p a = i
    · have hai : a ∈ s.filter fun j => p j = i := by simp [ha, hpa]
      have hbi : b ∈ (s.filter fun j => p j = i).erase a := by simp [hab, hb, hpab, hpa]
      rw [Finset.card_erase_of_mem hbi, Finset.card_erase_of_mem hai]
      obtain ⟨k, hk⟩ := h i
      have hsub : ({a, b} : Finset J) ⊆ s.filter fun j => p j = i := by
        intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> [exact hai; simp [hb, hpab, hpa]]
      have h2 : 2 ≤ (s.filter fun j => p j = i).card := by
        simpa [Ne.symm hab] using Finset.card_le_card hsub
      exact ⟨k - 1, by omega⟩
    · simp only [Finset.erase_eq_of_notMem (show a ∉ s.filter fun j => p j = i by simp [hpa]),
        Finset.erase_eq_of_notMem (show b ∉ s.filter fun j => p j = i by simp [hpab, hpa])]
      exact h i
  obtain ⟨e, he, hec, hpec⟩ := hpart heven hc
  have hct := Finset.mem_erase.mp hc; have hct' := Finset.mem_erase.mp hct.2
  have het := Finset.mem_erase.mp he; have het' := Finset.mem_erase.mp het.2
  exact ⟨a, ha, b, hb, c, hct'.2, e, het'.2, hab, hct'.1, hct.1, het'.1, het.1, hec, hpab, hpec⟩

abbrev partitionFieldFiber (H : Type*) (n : ℕ) :=
  (Fin n → H) × ((Fin n → Fin 2) → Fin 2)

abbrev partitionFieldMark (H : Type*) := Σ n : ℕ, partitionFieldFiber H n

instance partitionFieldMark_standardBorel {H : Type*} [MeasurableSpace H] [StandardBorelSpace H] :
    StandardBorelSpace (partitionFieldMark H) := sigma_standardBorel_actual

abbrev CellMomentQuadruple (j : ℕ) := {q : Fin 4 → Fin j // Function.Injective q}

theorem cellMomentQuadruple_card_le (j : ℕ) :
    Fintype.card (CellMomentQuadruple j) ≤ j^4 := by
  simpa only [Fintype.card_fun, Fintype.card_fin] using
    Fintype.card_subtype_le fun q : Fin 4 → Fin j => Function.Injective q

section PoissonCell
variable {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]

def partitionFieldFiberLaw (μ : Measure H) (n : ℕ) : Measure (partitionFieldFiber H n) :=
  (Measure.pi fun _ : Fin n => μ).prod (cellSignLaw (Fin n → Fin 2))

instance partitionFieldFiberLaw_probability (μ : Measure H) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (partitionFieldFiberLaw μ n) := by
  unfold partitionFieldFiberLaw; infer_instance

def poissonCellFieldLaw (μ : Measure H) (r : ℝ≥0) : Measure (partitionFieldMark H) :=
  Measure.sum fun n => ENNReal.ofReal (Real.exp (-r) * (r : ℝ) ^ n / n.factorial) •
    (partitionFieldFiberLaw μ n).map (Sigma.mk n)

instance poissonCellFieldLaw_probability (μ : Measure H) [IsProbabilityMeasure μ] (r : ℝ≥0) :
    IsProbabilityMeasure (poissonCellFieldLaw μ r) := by
  constructor
  simp only [poissonCellFieldLaw, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply, smul_eq_mul]
  simp_rw [show ∀ n : ℕ, (partitionFieldFiberLaw μ n).map (Sigma.mk n) Set.univ = 1 from fun n => by
    rw [Measure.map_apply (measurable_sigma_mk_actual n) MeasurableSet.univ]; simp, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) (hasSum_one_poissonMeasure r).summable,
    (hasSum_one_poissonMeasure r).tsum_eq]
  simp

lemma poissonCellFieldLaw_measurable (μ : Measure H) :
    Measurable (poissonCellFieldLaw μ) :=
  Measure.measurable_of_measurable_coe _ fun s hs => by
    simp only [poissonCellFieldLaw, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
    exact Measurable.ennreal_tsum fun n =>
      (ENNReal.measurable_ofReal.comp
        (((measurable_coe_nnreal_real.neg.exp).mul
          (measurable_coe_nnreal_real.pow_const n)).div_const _)).mul_const _

def partitionFieldPattern (ρ : H → X → Fin 2) {n : ℕ}
    (h : Fin n → H) (x : X) : Fin n → Fin 2 := fun i => ρ (h i) x

def partitionFieldFiberValue (ρ : H → X → Fin 2) {n : ℕ}
    (z : partitionFieldFiber H n) (x : X) : ℝ :=
  fairSignValue (z.2 (partitionFieldPattern ρ z.1 x))

def poissonCellFieldValue (ρ : H → X → Fin 2)
    (z : partitionFieldMark H) (x : X) : ℝ := partitionFieldFiberValue ρ z.2 x

lemma partitionFieldFiberValue_abs (ρ : H → X → Fin 2) {n : ℕ}
    (z : partitionFieldFiber H n) (x : X) : |partitionFieldFiberValue ρ z x| = 1 :=
  fairSignValue_abs _

lemma poissonCellFieldValue_abs (ρ : H → X → Fin 2)
    (z : partitionFieldMark H) (x : X) : |poissonCellFieldValue ρ z x| = 1 :=
  fairSignValue_abs _

lemma partitionFieldPattern_measurable (ρ : H → X → Fin 2)
    (hρ : Measurable (Function.uncurry ρ)) (n : ℕ) :
    Measurable fun z : (Fin n → H) × X => partitionFieldPattern ρ z.1 z.2 := by
  apply Measurable.of_eval
  intro i
  change Measurable fun z : (Fin n → H) × X => ρ (z.1 i) z.2
  have he : Measurable fun z : (Fin n → H) × X => (z.1 i, z.2) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
  exact hρ.comp he

lemma partitionFieldFiberValue_measurable (ρ : H → X → Fin 2)
    (hρ : Measurable (Function.uncurry ρ)) (n : ℕ) :
    Measurable fun z : partitionFieldFiber H n × X => partitionFieldFiberValue ρ z.1 z.2 := by
  have hp : Measurable fun z : partitionFieldFiber H n × X => partitionFieldPattern ρ z.1.1 z.2 :=
    (partitionFieldPattern_measurable ρ hρ n).comp (measurable_fst.fst.prodMk measurable_snd)
  have heval : Measurable fun z : partitionFieldFiber H n × X => z.1.2 (partitionFieldPattern ρ z.1.1 z.2) := by
    intro s hs
    rw [show (fun z : partitionFieldFiber H n × X => z.1.2 (partitionFieldPattern ρ z.1.1 z.2)) ⁻¹' s =
      ⋃ p : Fin n → Fin 2, (fun z : partitionFieldFiber H n × X => partitionFieldPattern ρ z.1.1 z.2) ⁻¹' {p} ∩
        (fun z : partitionFieldFiber H n × X => z.1.2 p) ⁻¹' s by ext; simp]
    exact MeasurableSet.iUnion fun p =>
      (hp (measurableSet_singleton p)).inter (measurable_fst.snd.eval hs)
  exact (Measurable.of_discrete : Measurable fairSignValue).comp heval

lemma poissonCellFieldValue_measurable_fixed (ρ : H → X → Fin 2)
    (hρ : Measurable (Function.uncurry ρ)) (x : X) :
    Measurable fun z : partitionFieldMark H => poissonCellFieldValue ρ z x :=
  measurable_sigma_of_fibers _ fun n =>
    (partitionFieldFiberValue_measurable ρ hρ n).comp (measurable_id.prodMk measurable_const)

lemma poissonCellFieldValue_measurable [StandardBorelSpace H] [StandardBorelSpace X]
    (ρ : H → X → Fin 2) (hρ : Measurable (Function.uncurry ρ)) :
    Measurable fun z : partitionFieldMark H × X => poissonCellFieldValue ρ z.1 z.2 := by
  letI : TopologicalSpace H := (upgradeStandardBorel H).toTopologicalSpace
  letI : BorelSpace H := (upgradeStandardBorel H).toBorelSpace
  letI : TopologicalSpace X := (upgradeStandardBorel X).toTopologicalSpace
  letI : BorelSpace X := (upgradeStandardBorel X).toBorelSpace
  letI : BorelSpace (partitionFieldMark H) := sigma_borelSpace_actual
  letI : BorelSpace (Σ n : ℕ, partitionFieldFiber H n × X) := sigma_borelSpace_actual
  exact (measurable_sigma_of_fibers
    (fun z : Σ n : ℕ, partitionFieldFiber H n × X => partitionFieldFiberValue ρ z.2.1 z.2.2)
    (partitionFieldFiberValue_measurable ρ hρ)).comp Homeomorph.sigmaProdDistrib.measurable

lemma poissonCellField_integral_series (μ : Measure H) [IsProbabilityMeasure μ]
    (r : ℝ≥0) (f : partitionFieldMark H → ℝ) (hf : Measurable f)
    (hfbound : ∀ z, |f z| ≤ 1) :
    (∫ z, f z ∂poissonCellFieldLaw μ r) =
      ∑' n, (Real.exp (-r) * (r : ℝ) ^ n / n.factorial) *
        ∫ z, f ⟨n, z⟩ ∂partitionFieldFiberLaw μ n := by
  have hi : Integrable f (poissonCellFieldLaw μ r) :=
    Integrable.of_bound hf.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hfbound z)
  rw [poissonCellFieldLaw, integral_sum_measure hi]
  refine tsum_congr fun n => ?_
  rw [integral_smul_measure, integral_map (measurable_sigma_mk_actual n).aemeasurable hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal (show 0 ≤ Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial by positivity), smul_eq_mul]

def partitionSameProbability (μ : Measure H) (ρ : H → X → Fin 2) (x y : X) : ℝ :=
  ∫ h, if ρ h x = ρ h y then (1 : ℝ) else 0 ∂μ

lemma poisson_weighted_power_hasSum (r : ℝ≥0) (p : ℝ) :
    HasSum (fun n : ℕ => (Real.exp (-r) * (r : ℝ) ^ n / n.factorial) * p ^ n)
      (Real.exp (-(r : ℝ) * (1 - p))) := by
  convert (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * p)).mul_left (Real.exp (-(r : ℝ))) using 1
  · ext n; rw [mul_pow]; ring
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]; congr 1; ring

lemma poissonCellField_covariance (μ : Measure H) [IsProbabilityMeasure μ]
    (r : ℝ≥0) (ρ : H → X → Fin 2) (hρ : Measurable (Function.uncurry ρ)) (x y : X) :
    (∫ z, poissonCellFieldValue ρ z x * poissonCellFieldValue ρ z y
      ∂poissonCellFieldLaw μ r) =
        Real.exp (-(r : ℝ) * (1 - partitionSameProbability μ ρ x y)) := by
  rw [poissonCellField_integral_series μ r
    (fun z => poissonCellFieldValue ρ z x * poissonCellFieldValue ρ z y)
    ((poissonCellFieldValue_measurable_fixed ρ hρ x).mul (poissonCellFieldValue_measurable_fixed ρ hρ y))
    fun _ => by simp only [abs_mul, poissonCellFieldValue_abs, mul_one, le_refl]]
  have hfib (n : ℕ) : (∫ z, partitionFieldFiberValue ρ z x * partitionFieldFiberValue ρ z y
      ∂partitionFieldFiberLaw μ n) = partitionSameProbability μ ρ x y ^ n := by
    have hm : Measurable fun z : partitionFieldFiber H n =>
        partitionFieldFiberValue ρ z x * partitionFieldFiberValue ρ z y :=
      ((partitionFieldFiberValue_measurable ρ hρ n).comp (measurable_id.prodMk measurable_const)).mul
        ((partitionFieldFiberValue_measurable ρ hρ n).comp (measurable_id.prodMk measurable_const))
    have hi : Integrable (fun z : partitionFieldFiber H n =>
        partitionFieldFiberValue ρ z x * partitionFieldFiberValue ρ z y) (partitionFieldFiberLaw μ n) :=
      Integrable.of_bound hm.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun _ => by simp only [Real.norm_eq_abs, abs_mul, partitionFieldFiberValue_abs, mul_one, le_refl])
    rw [partitionFieldFiberLaw, integral_prod _ hi]
    simp only [partitionFieldFiberValue, cellSign_covariance]
    simp_rw [show ∀ h : Fin n → H,
      (if partitionFieldPattern ρ h x = partitionFieldPattern ρ h y then (1 : ℝ) else 0) =
        ∏ i : Fin n, if ρ (h i) x = ρ (h i) y then (1 : ℝ) else 0 from fun _ => by
      rw [Fintype.prod_boole]; simp only [partitionFieldPattern, funext_iff]; split_ifs <;> rfl]
    rw [integral_fintype_prod_eq_pow fun h => if ρ h x = ρ h y then (1 : ℝ) else 0]
    simp only [Fintype.card_fin, partitionSameProbability]
  simp only [poissonCellFieldValue, hfib]
  exact (poisson_weighted_power_hasSum r (partitionSameProbability μ ρ x y)).tsum_eq

section HigherMoment
attribute [local instance] Classical.propDecidable

lemma poissonCellField_product_moment_abs_le_two_pairs
    (μ : Measure H) [IsProbabilityMeasure μ] (r : ℝ≥0)
    (ρ : H → X → Fin 2) (hρ : Measurable (Function.uncurry ρ))
    (j : ℕ) (hj : 4 ≤ j) (U : Fin j → X) :
    |∫ z, ∏ l, poissonCellFieldValue ρ z (U l) ∂poissonCellFieldLaw μ r| ≤
      ∑ q : CellMomentQuadruple j, Real.exp (-(r : ℝ) / 2 *
        ((1 - partitionSameProbability μ ρ (U (q.val 0)) (U (q.val 1))) +
          (1 - partitionSameProbability μ ρ (U (q.val 2)) (U (q.val 3))))) := by
  let pairInd (x y : X) (h : H) : ℝ := if ρ h x = ρ h y then 1 else 0
  have hpairM (x y : X) : Measurable (pairInd x y) :=
    Measurable.ite (measurableSet_eq_fun (hρ.comp (measurable_id.prodMk measurable_const))
      (hρ.comp (measurable_id.prodMk measurable_const))) measurable_const measurable_const
  have hpairI (x y : X) : Integrable (pairInd x y) μ :=
    Integrable.of_bound (hpairM x y).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun _ => by dsimp [pairInd]; split_ifs <;> norm_num)
  let bothProb (q : CellMomentQuadruple j) : ℝ :=
    ∫ h, pairInd (U (q.val 0)) (U (q.val 1)) h * pairInd (U (q.val 2)) (U (q.val 3)) h ∂μ
  let wt (n : ℕ) : ℝ := Real.exp (-r) * (r : ℝ) ^ n / n.factorial
  have hwt (n : ℕ) : 0 ≤ wt n := by dsimp [wt]; positivity
  have hfib (n : ℕ) : 0 ≤ (∫ z, ∏ l, partitionFieldFiberValue ρ z (U l) ∂partitionFieldFiberLaw μ n) ∧
      (∫ z, ∏ l, partitionFieldFiberValue ρ z (U l) ∂partitionFieldFiberLaw μ n) ≤
        ∑ q : CellMomentQuadruple j, bothProb q ^ n := by
    have hiF : Integrable (fun z : partitionFieldFiber H n => ∏ l, partitionFieldFiberValue ρ z (U l))
        (partitionFieldFiberLaw μ n) :=
      Integrable.of_bound (Finset.measurable_prod _ fun l _ =>
        (partitionFieldFiberValue_measurable ρ hρ n).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun _ => by
          simp only [Real.norm_eq_abs, Finset.abs_prod, partitionFieldFiberValue_abs, Finset.prod_const_one, le_refl])
    rw [partitionFieldFiberLaw, integral_prod _ hiF]
    simp only [partitionFieldFiberValue, cellSign_product_moment]
    let evInd (h : Fin n → H) : ℝ :=
      if ∀ p : Fin n → Fin 2, Even ((Finset.univ.filter fun l => partitionFieldPattern ρ h (U l) = p).card)
        then 1 else 0
    let bInd (q : CellMomentQuadruple j) (h : Fin n → H) : ℝ :=
      if partitionFieldPattern ρ h (U (q.val 0)) = partitionFieldPattern ρ h (U (q.val 1)) ∧
        partitionFieldPattern ρ h (U (q.val 2)) = partitionFieldPattern ρ h (U (q.val 3)) then 1 else 0
    have hevM : Measurable evInd :=
      (measurable_of_finite fun p : Fin j → Fin n → Fin 2 =>
        if ∀ c : Fin n → Fin 2, Even ((Finset.univ.filter fun l => p l = c).card) then (1 : ℝ) else 0).comp
        (Measurable.of_eval fun l => (partitionFieldPattern_measurable ρ hρ n).comp (measurable_id.prodMk measurable_const))
    have hevI : Integrable evInd (Measure.pi fun _ : Fin n => μ) :=
      Integrable.of_bound hevM.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun _ => by dsimp [evInd]; split_ifs <;> norm_num)
    have hpatM := partitionFieldPattern_measurable ρ hρ n
    have hbI (q : CellMomentQuadruple j) : Integrable (bInd q) (Measure.pi fun _ : Fin n => μ) := by
      have hm : Measurable (bInd q) :=
        Measurable.ite ((measurableSet_eq_fun (hpatM.comp (measurable_id.prodMk measurable_const))
            (hpatM.comp (measurable_id.prodMk measurable_const))).inter
          (measurableSet_eq_fun (hpatM.comp (measurable_id.prodMk measurable_const))
            (hpatM.comp (measurable_id.prodMk measurable_const))))
          measurable_const measurable_const
      exact Integrable.of_bound hm.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun _ => by dsimp [bInd]; split_ifs <;> norm_num)
    have hpt (h : Fin n → H) : evInd h ≤ ∑ q : CellMomentQuadruple j, bInd q h := by
      dsimp [evInd]; split_ifs with heven
      · obtain ⟨a, _, b, _, c, _, e, _, hba, hca, hcb, hea, heb, hec, hab, hce⟩ :=
          even_cells_two_disjoint_pairs (Finset.univ : Finset (Fin j))
            (fun l => partitionFieldPattern ρ h (U l)) (by simpa using hj) heven
        let q : CellMomentQuadruple j := ⟨![a, b, c, e], fun i l hil => by fin_cases i <;> fin_cases l <;> simp_all⟩
        have hq : bInd q h = 1 := by
          simp only [bInd, q, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
          simp [hab.symm, hce.symm]
        rw [← hq]
        exact Finset.single_le_sum (f := fun q' => bInd q' h)
          (fun q' _ => by simp only [bInd]; split_ifs <;> norm_num) (Finset.mem_univ q)
      · exact Finset.sum_nonneg fun q' _ => by simp only [bInd]; split_ifs <;> norm_num
    have hbInt (q : CellMomentQuadruple j) : (∫ h, bInd q h ∂Measure.pi fun _ : Fin n => μ) = bothProb q ^ n := by
      have he (h : Fin n → H) : bInd q h =
          ∏ i : Fin n, pairInd (U (q.val 0)) (U (q.val 1)) (h i) * pairInd (U (q.val 2)) (U (q.val 3)) (h i) := by
        simp_rw [show ∀ z : H, pairInd (U (q.val 0)) (U (q.val 1)) z * pairInd (U (q.val 2)) (U (q.val 3)) z =
          if ρ z (U (q.val 0)) = ρ z (U (q.val 1)) ∧ ρ z (U (q.val 2)) = ρ z (U (q.val 3)) then (1 : ℝ) else 0
          from fun _ => by dsimp [pairInd]; split_ifs <;> norm_num <;> aesop]
        dsimp [bInd]; rw [Fintype.prod_boole]
        simp only [partitionFieldPattern, funext_iff, forall_and]
      simp_rw [he]
      rw [integral_fintype_prod_eq_pow fun h =>
        pairInd (U (q.val 0)) (U (q.val 1)) h * pairInd (U (q.val 2)) (U (q.val 3)) h]
      simp only [bothProb, Fintype.card_fin]
    refine ⟨integral_nonneg fun _ => by split_ifs <;> norm_num, ?_⟩
    exact (integral_mono hevI (integrable_finsetSum Finset.univ fun q _ => hbI q) hpt).trans_eq
      (by rw [integral_finsetSum Finset.univ fun q _ => hbI q]; exact Finset.sum_congr rfl fun q _ => hbInt q)
  rw [poissonCellField_integral_series μ r (fun z => ∏ l, poissonCellFieldValue ρ z (U l))
    (Finset.measurable_prod _ fun l _ => poissonCellFieldValue_measurable_fixed ρ hρ (U l))
    fun _ => by simp only [Finset.abs_prod, poissonCellFieldValue_abs, Finset.prod_const_one, le_refl]]
  simp only [poissonCellFieldValue]
  rw [abs_of_nonneg (tsum_nonneg fun n => mul_nonneg (hwt n) (hfib n).1)]
  have hsum_le : (∑' n, wt n * ∫ z, ∏ l, partitionFieldFiberValue ρ z (U l) ∂partitionFieldFiberLaw μ n) ≤
      ∑ q : CellMomentQuadruple j, Real.exp (-(r : ℝ) * (1 - bothProb q)) := by
    have hqSum (q : CellMomentQuadruple j) := poisson_weighted_power_hasSum r (bothProb q)
    have hmaj : Summable fun n => ∑ q : CellMomentQuadruple j, wt n * bothProb q ^ n :=
      summable_sum fun q _ => (hqSum q).summable
    have hterm : Summable fun n => wt n * ∫ z, ∏ l, partitionFieldFiberValue ρ z (U l) ∂partitionFieldFiberLaw μ n :=
      Summable.of_nonneg_of_le (fun n => mul_nonneg (hwt n) (hfib n).1)
        (fun n => (mul_le_mul_of_nonneg_left (hfib n).2 (hwt n)).trans_eq (Finset.mul_sum _ _ _)) hmaj
    refine (hterm.tsum_le_tsum (fun n => (mul_le_mul_of_nonneg_left (hfib n).2 (hwt n)).trans_eq (Finset.mul_sum _ _ _)) hmaj).trans_eq ?_
    rw [Summable.tsum_finsetSum fun q _ => (hqSum q).summable]
    exact Finset.sum_congr rfl fun q _ => (hqSum q).tsum_eq
  refine hsum_le.trans (Finset.sum_le_sum fun q _ => Real.exp_le_exp.mpr ?_)
  have hp : Integrable (fun h => pairInd (U (q.val 0)) (U (q.val 1)) h * pairInd (U (q.val 2)) (U (q.val 3)) h) μ :=
    Integrable.of_bound ((hpairM _ _).mul (hpairM _ _)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun _ => by dsimp [pairInd]; split_ifs <;> norm_num)
  have hhalf : bothProb q ≤ (partitionSameProbability μ ρ (U (q.val 0)) (U (q.val 1)) +
      partitionSameProbability μ ρ (U (q.val 2)) (U (q.val 3))) / 2 := by
    have h := integral_mono hp (((hpairI _ _).add (hpairI _ _)).div_const 2) fun h =>
      show pairInd (U (q.val 0)) (U (q.val 1)) h * pairInd (U (q.val 2)) (U (q.val 3)) h ≤
        (pairInd (U (q.val 0)) (U (q.val 1)) h + pairInd (U (q.val 2)) (U (q.val 3)) h) / 2 by
          dsimp [pairInd]; split_ifs <;> norm_num
    rw [integral_div] at h
    change bothProb q ≤ (∫ h, pairInd (U (q.val 0)) (U (q.val 1)) h + pairInd (U (q.val 2)) (U (q.val 3)) h ∂μ) / 2 at h
    rwa [integral_add (hpairI _ _) (hpairI _ _)] at h
  nlinarith only [hhalf, r.coe_nonneg]

end HigherMoment
end PoissonCell

section GaussianHyperplane
open scoped RealInnerProductSpace

def gaussianAbsoluteMean : ℝ := ∫ z : ℝ, |z| ∂standardGaussianLine

lemma gaussianAbsoluteMean_pos : 0 < gaussianAbsoluteMean := by
  have hn : 0 ≤ gaussianAbsoluteMean := integral_nonneg fun _ => abs_nonneg _
  by_contra h
  have hz : gaussianAbsoluteMean = 0 := le_antisymm (not_lt.mp h) hn
  have hi : Integrable (fun z : ℝ => |z|) standardGaussianLine := by
    simpa only [Real.norm_eq_abs, id_eq] using (IsGaussian.integrable_id (μ := standardGaussianLine)).norm
  have habs : (fun z : ℝ => |z|) =ᵐ[standardGaussianLine] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => abs_nonneg z) hi).mp hz
  have hv := variance_congr (habs.mono fun _ => abs_eq_zero.mp : id =ᵐ[standardGaussianLine] fun _ : ℝ => (0 : ℝ))
  rw [variance_id_gaussianReal] at hv
  change (1 : ℝ) = Var[(0 : ℝ → ℝ); standardGaussianLine] at hv
  rw [variance_zero] at hv
  exact one_ne_zero hv

lemma gaussianPhase_abs_integral {d : ℕ} (v : Covariate d) :
    (∫ Z, |gaussianPhase v Z| ∂standardGaussianPi d) = gaussianAbsoluteMean * euclideanNorm v := by
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin d)) := innerSL ℝ (WithLp.toLp 2 v)
  have hfun : gaussianPhase v = L ∘ WithLp.toLp 2 := funext fun Z => by
    dsimp [L]
    simp only [gaussianPhase, innerSL_apply_apply, PiLp.inner_apply,
      WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial, mul_comm]
  have hnorm : euclideanNorm v = ‖WithLp.toLp 2 v‖ := by
    rw [EuclideanSpace.norm_eq]; unfold euclideanNorm
    congr 1; refine Finset.sum_congr rfl fun r _ => ?_
    simp only [WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs]
  have hmap : (standardGaussianPi d).map (gaussianPhase v) =
      standardGaussianLine.map fun z : ℝ => euclideanNorm v * z := by
    rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), map_pi_eq_stdGaussian,
      IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, gaussianReal_map_const_mul]
    simp only [mul_zero, mul_one]; congr 1
    apply NNReal.coe_injective; rw [Real.coe_toNNReal _ (sq_nonneg _)]
    simp only [L, innerSL_apply_norm, hnorm]
    rfl
  have hphase : Measurable (gaussianPhase v) := by unfold gaussianPhase; fun_prop
  rw [← integral_map hphase.aemeasurable (by fun_prop : Measurable fun z : ℝ => |z|).aestronglyMeasurable,
    hmap, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, abs_of_nonneg (show 0 ≤ euclideanNorm v by unfold euclideanNorm; positivity)]
  rw [integral_const_mul]; exact mul_comm _ _

end GaussianHyperplane

def hyperplaneRadius {d : ℕ} (Z : Covariate d) : ℝ := ∑ r, |Z r|
def hyperplaneCube (d : ℕ) : Set (Covariate d) := {u | ∀ r, |u r| ≤ 1}
def hyperplaneSlab (d : ℕ) : Set (Covariate d × ℝ) := {h | |h.2| ≤ hyperplaneRadius h.1}

def gaussianHyperplaneIntensity (d : ℕ) : Measure (Covariate d × ℝ) :=
  ((standardGaussianPi d).prod volume).restrict (hyperplaneSlab d)

def hyperplaneHalfspace {d : ℕ} (h : Covariate d × ℝ) (u : Covariate d) : Fin 2 :=
  if gaussianPhase u h.1 ≤ h.2 then 0 else 1

lemma hyperplaneHalfspace_measurable {d : ℕ} :
    Measurable (Function.uncurry (hyperplaneHalfspace (d := d))) := by
  have hp : Measurable fun z : (Covariate d × ℝ) × Covariate d => gaussianPhase z.2 z.1.1 := by
    unfold gaussianPhase; fun_prop
  exact Measurable.ite (measurableSet_le hp measurable_fst.snd) measurable_const measurable_const

def hyperplaneSeparationSet {d : ℕ} (u v : Covariate d) : Set (Covariate d × ℝ) :=
  {h | hyperplaneHalfspace h u ≠ hyperplaneHalfspace h v}

lemma hyperplaneSeparationSet_measurable {d : ℕ} (u v : Covariate d) :
    MeasurableSet (hyperplaneSeparationSet u v) :=
  (measurableSet_eq_fun
    (hyperplaneHalfspace_measurable.comp (measurable_id.prodMk measurable_const))
    (hyperplaneHalfspace_measurable.comp (measurable_id.prodMk measurable_const))).compl

lemma hyperplane_separation_slice {d : ℕ} (Z u v : Covariate d) :
    (fun b : ℝ => (Z, b)) ⁻¹' hyperplaneSeparationSet u v =
      Ico (min (gaussianPhase u Z) (gaussianPhase v Z))
        (max (gaussianPhase u Z) (gaussianPhase v Z)) := by
  ext b; unfold hyperplaneSeparationSet hyperplaneHalfspace
  simp only [mem_preimage, mem_setOf_eq, mem_Ico]
  rcases le_total (gaussianPhase u Z) (gaussianPhase v Z) with huv | hvu
  · rw [min_eq_left huv, max_eq_right huv]; split_ifs <;> norm_num <;> grind
  · rw [min_eq_right hvu, max_eq_left hvu]; split_ifs <;> norm_num <;> grind

lemma hyperplane_coordinate_integrable {d : ℕ} (r : Fin d) :
    Integrable (fun Z : Covariate d => Z r) (standardGaussianPi d) :=
  integrable_comp_eval (μ := fun _ : Fin d => standardGaussianLine) (i := r) (f := id)
    ((memLp_id_gaussianReal (μ := 0) (v := 1) (1 : ℝ≥0)).integrable (by norm_num))

def hyperplaneNormalizingConstant (d : ℕ) : ℝ :=
  ∫ Z, 2 * hyperplaneRadius Z ∂standardGaussianPi d

lemma hyperplaneNormalizingConstant_eq (d : ℕ) :
    hyperplaneNormalizingConstant d = 2 * d * gaussianAbsoluteMean := by
  rw [hyperplaneNormalizingConstant, integral_const_mul]
  unfold hyperplaneRadius
  rw [integral_finsetSum _ fun r _ => (hyperplane_coordinate_integrable r).abs]
  simp_rw [show ∀ r : Fin d, (∫ Z : Covariate d, |Z r| ∂standardGaussianPi d) = gaussianAbsoluteMean from
    fun r => integral_comp_eval (μ := fun _ : Fin d => standardGaussianLine)
      (f := fun z : ℝ => |z|) (i := r) (by fun_prop)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma hyperplaneNormalizingConstant_pos (d : ℕ) [NeZero d] :
    0 < hyperplaneNormalizingConstant d := by
  rw [hyperplaneNormalizingConstant_eq]
  exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr (NeZero.pos d))) gaussianAbsoluteMean_pos

def gaussianHyperplaneLaw (d : ℕ) : Measure (Covariate d × ℝ) :=
  (ENNReal.ofReal (hyperplaneNormalizingConstant d))⁻¹ • gaussianHyperplaneIntensity d

instance gaussianHyperplaneLaw_probability (d : ℕ) [NeZero d] :
    IsProbabilityMeasure (gaussianHyperplaneLaw d) := by
  constructor
  have hslab : MeasurableSet (hyperplaneSlab d) :=
    measurableSet_le measurable_snd.abs
      ((by unfold hyperplaneRadius; fun_prop : Continuous (hyperplaneRadius (d := d))).measurable.comp measurable_fst)
  have huniv : gaussianHyperplaneIntensity d univ = ENNReal.ofReal (hyperplaneNormalizingConstant d) := by
    rw [gaussianHyperplaneIntensity, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Measure.prod_apply hslab]
    simp_rw [show ∀ Z : Covariate d, (fun b : ℝ => (Z, b)) ⁻¹' hyperplaneSlab d =
      Icc (-hyperplaneRadius Z) (hyperplaneRadius Z) from fun _ => by
        ext; simp [hyperplaneSlab, abs_le], Real.volume_Icc,
      show ∀ Z : Covariate d, hyperplaneRadius Z - -hyperplaneRadius Z = 2 * hyperplaneRadius Z from fun _ => by ring]
    exact (ofReal_integral_eq_lintegral_ofReal
      ((integrable_finsetSum _ fun r _ => (hyperplane_coordinate_integrable r).abs).const_mul 2)
      (Filter.Eventually.of_forall fun _ => mul_nonneg zero_le_two (Finset.sum_nonneg fun _ _ => abs_nonneg _))).symm
  rw [gaussianHyperplaneLaw, Measure.smul_apply, smul_eq_mul, huniv]
  exact ENNReal.inv_mul_cancel (by simp [hyperplaneNormalizingConstant_pos d]) ENNReal.ofReal_ne_top

lemma gaussianHyperplaneLaw_same_complement_eq (d : ℕ) [NeZero d] (u v : Covariate d)
    (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d) :
    1 - partitionSameProbability (gaussianHyperplaneLaw d) hyperplaneHalfspace u v =
      euclideanNorm (fun r => u r - v r) / (2 * d) := by
  let s : Set (Covariate d × ℝ) := {h | hyperplaneHalfspace h u = hyperplaneHalfspace h v}
  have hs : MeasurableSet s := (hyperplaneSeparationSet_measurable u v).of_compl
  have he : partitionSameProbability (gaussianHyperplaneLaw d) hyperplaneHalfspace u v =
      (gaussianHyperplaneLaw d).real s := by
    simpa only [partitionSameProbability, s, Set.indicator, Pi.one_apply, Set.mem_setOf_eq] using
      integral_indicator_one (μ := gaussianHyperplaneLaw d) hs
  rw [he, show 1 - (gaussianHyperplaneLaw d).real s = (gaussianHyperplaneLaw d).real (hyperplaneSeparationSet u v) by
    change 1 - (gaussianHyperplaneLaw d).real s = (gaussianHyperplaneLaw d).real sᶜ
    rw [measureReal_compl hs]; simp]
  have hsub : hyperplaneSeparationSet u v ⊆ hyperplaneSlab d := fun h hh => by
    have hs0 := (Set.ext_iff.mp (hyperplane_separation_slice h.1 u v) h.2).mp hh
    have hpB {w : Covariate d} (hw : w ∈ hyperplaneCube d) : |gaussianPhase w h.1| ≤ hyperplaneRadius h.1 :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => by
        rw [abs_mul]; simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw r) (abs_nonneg _))
    have hu' := abs_le.mp (hpB hu); have hv' := abs_le.mp (hpB hv)
    exact abs_le.mpr ⟨(le_min hu'.1 hv'.1).trans hs0.1, hs0.2.le.trans (max_le hu'.2 hv'.2)⟩
  have hsep : gaussianHyperplaneIntensity d (hyperplaneSeparationSet u v) =
      ENNReal.ofReal (∫ Z, |gaussianPhase u Z - gaussianPhase v Z| ∂standardGaussianPi d) := by
    rw [gaussianHyperplaneIntensity, Measure.restrict_apply (hyperplaneSeparationSet_measurable u v),
      inter_eq_left.mpr hsub, Measure.prod_apply (hyperplaneSeparationSet_measurable u v)]
    simp_rw [hyperplane_separation_slice, Real.volume_Ico, max_sub_min_eq_abs, abs_sub_comm]
    have hph (w : Covariate d) : Integrable (gaussianPhase w) (standardGaussianPi d) :=
      integrable_finsetSum _ fun r _ => (hyperplane_coordinate_integrable r).const_mul (w r)
    exact (ofReal_integral_eq_lintegral_ofReal ((hph u).sub (hph v)).abs
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)).symm
  rw [gaussianHyperplaneLaw, measureReal_ennreal_smul_apply, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (hyperplaneNormalizingConstant_pos d).le, measureReal_def, hsep,
    ENNReal.toReal_ofReal (integral_nonneg fun _ => abs_nonneg _)]
  simp_rw [show ∀ Z : Covariate d, gaussianPhase u Z - gaussianPhase v Z = gaussianPhase (fun r => u r - v r) Z from
    fun _ => by simp only [gaussianPhase, sub_mul, Finset.sum_sub_distrib]]
  rw [gaussianPhase_abs_integral, hyperplaneNormalizingConstant_eq]
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hg := gaussianAbsoluteMean_pos.ne'
  field_simp

def boundedHyperplaneFieldLaw (d : ℕ) (T : ℝ) : Measure (partitionFieldMark (Covariate d × ℝ)) :=
  poissonCellFieldLaw (gaussianHyperplaneLaw d) (Real.toNNReal (2 * d * T))

def boundedHyperplaneFieldValue {d : ℕ} (z : partitionFieldMark (Covariate d × ℝ))
    (u : Covariate d) : ℝ := poissonCellFieldValue hyperplaneHalfspace z u

instance boundedHyperplaneFieldLaw_probability (d : ℕ) [NeZero d] (T : ℝ) :
    IsProbabilityMeasure (boundedHyperplaneFieldLaw d T) := by
  unfold boundedHyperplaneFieldLaw; infer_instance

theorem boundedHyperplaneFieldLaw_measurable (d : ℕ) :
    Measurable (boundedHyperplaneFieldLaw d) :=
  (poissonCellFieldLaw_measurable (gaussianHyperplaneLaw d)).comp
    (measurable_real_toNNReal.comp (measurable_const.mul measurable_id))

theorem boundedHyperplaneFieldValue_measurable (d : ℕ) :
    Measurable fun z : partitionFieldMark (Covariate d × ℝ) × Covariate d =>
      boundedHyperplaneFieldValue z.1 z.2 :=
  poissonCellFieldValue_measurable hyperplaneHalfspace hyperplaneHalfspace_measurable

theorem boundedHyperplaneFieldValue_abs {d : ℕ}
    (z : partitionFieldMark (Covariate d × ℝ)) (u : Covariate d) :
    |boundedHyperplaneFieldValue z u| = 1 := poissonCellFieldValue_abs _ _ _

theorem boundedHyperplaneField_covariance (d : ℕ) [NeZero d] (T : ℝ) (hT : 0 ≤ T)
    (u v : Covariate d) (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d) :
    (∫ z, boundedHyperplaneFieldValue z u * boundedHyperplaneFieldValue z v
      ∂boundedHyperplaneFieldLaw d T) =
      Real.exp (-T * euclideanNorm fun r => u r - v r) := by
  simp only [boundedHyperplaneFieldLaw, boundedHyperplaneFieldValue]
  rw [poissonCellField_covariance _ _ _ hyperplaneHalfspace_measurable,
    gaussianHyperplaneLaw_same_complement_eq d u v hu hv,
    Real.coe_toNNReal (2 * (d : ℝ) * T) (by positivity)]
  congr 1
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  field_simp

theorem boundedHyperplaneField_higher_moment_envelope (d : ℕ) [NeZero d]
    (T : ℝ) (hT : 0 ≤ T) (j : ℕ) (hj : 4 ≤ j) (U : Fin j → Covariate d)
    (hU : ∀ l, U l ∈ hyperplaneCube d) :
    |∫ z, ∏ l, boundedHyperplaneFieldValue z (U l) ∂boundedHyperplaneFieldLaw d T| ≤
      ∑ q : CellMomentQuadruple j, Real.exp (-T / 2 *
        (euclideanNorm (fun r => U (q.val 0) r - U (q.val 1) r) +
          euclideanNorm (fun r => U (q.val 2) r - U (q.val 3) r))) := by
  refine (poissonCellField_product_moment_abs_le_two_pairs (gaussianHyperplaneLaw d)
    (Real.toNNReal (2 * d * T)) hyperplaneHalfspace hyperplaneHalfspace_measurable j hj U).trans_eq
    (Finset.sum_congr rfl fun q _ => ?_)
  rw [gaussianHyperplaneLaw_same_complement_eq d _ _ (hU _) (hU _),
    gaussianHyperplaneLaw_same_complement_eq d _ _ (hU _) (hU _),
    Real.coe_toNNReal (2 * (d : ℝ) * T) (by positivity)]
  congr 1
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  field_simp

end PoissonHyperplaneField

end NearlyMinimax
