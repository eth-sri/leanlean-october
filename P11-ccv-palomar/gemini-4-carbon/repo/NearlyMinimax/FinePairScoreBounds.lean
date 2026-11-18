module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import NearlyMinimax.BoundedHyperplaneField

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped BigOperators ENNReal
namespace NearlyMinimax

-- ============================================================================
-- 1. Cardinal Product Design, Exponential/Laplace Kernels, and Spatial Products
-- ============================================================================

section SpatialKernelsAndProducts
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

lemma centered_cardinal_factor_continuous {d n : ℕ} (i : Fin n) (lam : ℝ)
    (z : CenteredCardinalMark d n i) (l : Fin n) : Continuous (centeredCardinalFactor i lam z l) := by
  unfold centeredCardinalFactor
  split_ifs
  · unfold gaussianPrimitiveRight gaussianTrig gaussianAffineFactor
    split_ifs <;> unfold gaussianPhase <;> fun_prop
  · refine continuous_finset_prod _ fun _ _ => ?_
    unfold gaussianPrimitiveLeft gaussianTrig
    split_ifs <;> unfold gaussianPhase <;> fun_prop

lemma cardinal_separated_factor_joint_measurable {d n : ℕ} (lam : ℝ) (l : Fin n) :
    Measurable fun zx : CardinalSeparatedMark d n × Covariate d =>
      cardinalSeparatedFactor lam zx.1 l zx.2 :=
  (measurable_uncurry_of_continuous_of_measurable
    (u := fun (x : Covariate d) (z : CardinalSeparatedMark d n) => cardinalSeparatedFactor lam z l x)
    (fun z => centered_cardinal_factor_continuous z.1 lam z.2 l)
    fun x => cardinal_separated_factor_measurable lam l x).comp measurable_swap

lemma cardinal_band_factor_joint_measurable {d n : ℕ} (lam : ℝ) (l : Fin n) :
    Measurable fun zx : CardinalBandMark d n × Covariate d =>
      cardinalBandFactor lam zx.1 l zx.2 :=
  (measurable_uncurry_of_continuous_of_measurable
    (u := fun (x : Covariate d) (z : CardinalBandMark d n) => cardinalBandFactor lam z l x)
    (fun z => centered_cardinal_factor_continuous z.2.1 lam z.2.2 l)
    fun x => cardinal_band_factor_measurable lam l x).comp measurable_swap

def cardinalHeadSplit {d n : ℕ} (i : Fin n) :
    (Fin n → Covariate d) ≃ᵐ Covariate d × (SpatialScaleIndex i → Covariate d) where
  toFun U := (U i, fun j => U j.val)
  invFun z := anchoredPatchConfiguration i z.1 z.2
  left_inv U := funext fun j => by
    change (if h : j ≠ i then U j else U i) = U j
    split_ifs with h
    · rfl
    · exact congrArg U (not_ne_iff.mp h).symm
  right_inv z := Prod.ext (anchored_configuration_same i z.1 z.2)
    (funext fun j => anchored_configuration_other i z.1 z.2 j)
  measurable_toFun := (measurable_pi_apply i).prodMk (Measurable.of_eval fun j => measurable_pi_apply j.val)
  measurable_invFun := Measurable.of_eval fun j => by
    change Measurable fun z : Covariate d × (SpatialScaleIndex i → Covariate d) =>
      if h : j ≠ i then z.2 ⟨j, h⟩ else z.1
    split_ifs <;> fun_prop

theorem cardinalHeadSplit_measurePreserving {d n : ℕ} (i : Fin n)
    (μ : Measure (Covariate d)) [SigmaFinite μ] :
    MeasurePreserving (cardinalHeadSplit i) (Measure.pi fun _ : Fin n => μ)
      (μ.prod (Measure.pi fun _ : SpatialScaleIndex i => μ)) := by
  letI : Unique {j : Fin n // j = i} := ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.property⟩
  have hs := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => μ) fun j => j = i
  rw [show (@Measure.pi {j : Fin n // j = i} (fun _ => Covariate d)
    (Subtype.fintype fun j => j = i) (fun _ => inferInstance) fun _ => μ) =
      Measure.pi fun _ : {j : Fin n // j = i} => μ by congr 1; exact Subsingleton.elim _ _] at hs
  exact ((measurePreserving_funUnique μ {j : Fin n // j = i}).prod
    (MeasurePreserving.id (Measure.pi fun _ : SpatialScaleIndex i => μ))).comp hs

def fullSpatialPatchDesign (d n : ℕ) : Measure (Fin n → Covariate d) :=
  Measure.pi fun _ : Fin n => volume.restrict (spatialPatchBox d)

def exactEuclideanDistance {d : ℕ} (x y : Covariate d) : ℝ :=
  Real.sqrt (spatialSquaredDistance x y)

theorem exactEuclideanDistance_nonneg {d : ℕ} (x y : Covariate d) :
    0 ≤ exactEuclideanDistance x y := Real.sqrt_nonneg _

lemma exactEuclideanDistance_eq_norm {d : ℕ} (x y : Covariate d) :
    exactEuclideanDistance x y = ‖WithLp.toLp 2 (y - x)‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold exactEuclideanDistance spatialSquaredDistance
  simp [Real.norm_eq_abs, sq_abs]

theorem exactEuclideanDistance_continuous {d : ℕ} :
    Continuous fun xy : Covariate d × Covariate d => exactEuclideanDistance xy.1 xy.2 := by
  unfold exactEuclideanDistance spatialSquaredDistance; fun_prop

def spatialExponentialConstant (d : ℕ) : ℝ :=
  (d : ℝ) * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) * Real.Gamma d

theorem spatialExponentialConstant_nonneg (d : ℕ) : 0 ≤ spatialExponentialConstant d := by
  unfold spatialExponentialConstant
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg d) ENNReal.toReal_nonneg)
    (Real.Gamma_nonneg_of_nonneg (Nat.cast_nonneg d))

lemma exactEuclideanDistance_exponential_integrable_and_integral {d : ℕ} (hd : 0 < d)
    {N : ℝ} (hN : 0 < N) (x : Covariate d) :
    Integrable (fun y => Real.exp (-(N * exactEuclideanDistance x y))) volume ∧
      (∫ y, Real.exp (-(N * exactEuclideanDistance x y))) = spatialExponentialConstant d / N^d := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hiE : Integrable (fun z : EuclideanSpace ℝ (Fin d) => Real.exp (-(N * ‖z‖))) volume := by
    refine (integrable_fun_norm_addHaar volume (f := fun r : ℝ => Real.exp (-(N*r)))).2 ?_
    simpa only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul,
      Real.rpow_natCast, Real.rpow_one, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (s := ((d-1 : ℕ) : ℝ)) (p := 1) (b := N)
        (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _)) (by norm_num) hN
  rw [← (PiLp.volume_preserving_toLp (Fin d)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 _).measurableEmbedding] at hiE
  have hi0 : Integrable (fun z : Covariate d => Real.exp (-(N * ‖WithLp.toLp 2 z‖))) volume := by
    simpa only [Function.comp_def] using hiE
  refine ⟨by simpa only [exactEuclideanDistance_eq_norm] using hi0.comp_sub_right x, ?_⟩
  simp_rw [exactEuclideanDistance_eq_norm]
  rw [integral_sub_right_eq_self (μ := volume) fun z : Covariate d => Real.exp (-(N * ‖WithLp.toLp 2 z‖)),
    (PiLp.volume_preserving_toLp (Fin d)).integral_comp (MeasurableEquiv.toLp 2 _).measurableEmbedding
      fun z : EuclideanSpace ℝ (Fin d) => Real.exp (-(N * ‖z‖)),
    integral_fun_norm_addHaar volume fun r : ℝ => Real.exp (-(N*r))]
  simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
  simp_rw [show ∀ r : ℝ, r^(d-1) = r^((d : ℝ)-1) from fun r => by
    rw [← Real.rpow_natCast, Nat.cast_sub hd, Nat.cast_one]]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by exact_mod_cast hd) hN, Real.rpow_natCast]
  unfold spatialExponentialConstant; simp only [div_pow, one_pow]; ring

theorem pair_defect_exponential_absorption (t : ℝ) (ht : 0 ≤ t) :
    (1+t)^2 * Real.exp (-(2*t)) ≤ 6 * Real.exp (-t) := by
  have hp := Real.pow_div_factorial_le_exp t ht 2
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, mul_one] at hp
  have h1 : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  have hh := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (t-1)] : (1+t)^2 ≤ 6 * Real.exp t)
    (Real.exp_nonneg (-(2*t)))
  rwa [mul_assoc, ← Real.exp_add, show t + -(2*t) = -t by ring] at hh

lemma spatialPatchBox_volume (d : ℕ) : volume (spatialPatchBox d) = (2 : ℝ≥0∞)^d := by
  simp only [spatialPatchBox, Real.volume_Icc_pi, sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

theorem spatialPatchBox_real_volume (d : ℕ) : volume.real (spatialPatchBox d) = (2 : ℝ)^d := by
  rw [measureReal_def, spatialPatchBox_volume, ENNReal.toReal_pow]; norm_num

instance spatialPatchBox_isFinite (d : ℕ) :
    IsFiniteMeasure (volume.restrict (spatialPatchBox d)) :=
  ⟨by rw [Measure.restrict_apply_univ, spatialPatchBox_volume]; finiteness⟩

instance fullSpatialPatchDesign_finite (d n : ℕ) : IsFiniteMeasure (fullSpatialPatchDesign d n) := by
  unfold fullSpatialPatchDesign; infer_instance

theorem fullSpatialPatchDesign_split {d n : ℕ} (i : Fin n)
    (f : (Fin n → Covariate d) → ℝ) :
    (∫ U, f U ∂fullSpatialPatchDesign d n) =
      ∫ z : Covariate d × (SpatialScaleIndex i → Covariate d),
        f (anchoredPatchConfiguration i z.1 z.2)
        ∂(volume.restrict (spatialPatchBox d)).prod (spatialPatchDesignMeasure i d) :=
  ((cardinalHeadSplit_measurePreserving i (volume.restrict (spatialPatchBox d))).symm.integral_comp' f).symm

theorem spatialPatchBox_pair_exponential_integral_le {d : ℕ} (hd : 0 < d)
    {T : ℝ} (hT : 0 < T) :
    (∫ xy : Covariate d × Covariate d, Real.exp (-(T * exactEuclideanDistance xy.1 xy.2))
      ∂(volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))) ≤
      (2 : ℝ)^d * spatialExponentialConstant d / T^d := by
  let μ : Measure (Covariate d) := volume.restrict (spatialPatchBox d)
  have hm : Measurable fun xy : Covariate d × Covariate d =>
      Real.exp (-(T * exactEuclideanDistance xy.1 xy.2)) :=
    (exactEuclideanDistance_continuous (d := d) |>.const_mul T |>.neg |>.rexp).measurable
  have hi : Integrable (fun xy : Covariate d × Covariate d =>
      Real.exp (-(T * exactEuclideanDistance xy.1 xy.2))) (μ.prod μ) :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun _ => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hT.le (exactEuclideanDistance_nonneg _ _))))
  rw [integral_prod _ hi]
  refine (integral_mono hi.integral_prod_left (integrable_const (spatialExponentialConstant d / T^d)) fun x =>
    (integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
      (exactEuclideanDistance_exponential_integrable_and_integral hd hT x).1).trans_eq
        (exactEuclideanDistance_exponential_integrable_and_integral hd hT x).2).trans_eq ?_
  simp only [integral_const, smul_eq_mul, μ, measureReal_def, Measure.restrict_apply_univ]
  change volume.real (spatialPatchBox d) * (spatialExponentialConstant d / T^d) = _
  rw [spatialPatchBox_real_volume]; ring

def pairLaplaceKernel (N r : ℝ) : ℝ := ∫ T in (0 : ℝ)..N, T * Real.exp (-(T*r))
def fineAliasLaplaceKernel (T0 N r : ℝ) : ℝ := ∫ T in T0..N, T * Real.exp (-(T*r))

theorem exactEuclideanDistance_eq_euclideanNorm {d : ℕ} (x y : Covariate d) :
    exactEuclideanDistance x y = euclideanNorm fun i => x i - y i := by
  unfold exactEuclideanDistance spatialSquaredDistance euclideanNorm
  congr 1; exact Finset.sum_congr rfl fun _ _ => by ring

lemma laplace_linear_tail {r : ℝ} (hr : 0 < r) (A : ℝ) :
    IntegrableOn (fun T : ℝ => T * Real.exp (-(T*r))) (Ici A) ∧
      (∫ T : ℝ in Ici A, T * Real.exp (-(T*r))) = (1 + A*r) * Real.exp (-(A*r)) / r^2 := by
  refine ⟨by simpa [mul_comm] using gamma_polynomial_tail_integrable hr A 1, ?_⟩
  have he : (∫ T : ℝ in Ici A, T * Real.exp (-(T*r))) = Real.exp (-(r*A)) * (1/r^2 + A/r) := by
    simpa [Finset.sum_range_succ, mul_comm] using gamma_polynomial_tail_integral hr A 1
  rw [he, mul_comm r A]; field_simp

lemma pairLaplaceKernel_defect (N r : ℝ) (hr : 0 ≤ r) :
    1 - r^2 * pairLaplaceKernel N r = (1+N*r) * Real.exp (-(N*r)) := by
  by_cases hr0 : r = 0
  · simp [hr0]
  · have hrp := lt_of_le_of_ne hr (Ne.symm hr0)
    have hf : pairLaplaceKernel N r = (1 - (1+N*r)*Real.exp (-(N*r))) / r^2 := by
      unfold pairLaplaceKernel
      rw [← intervalIntegral.integral_Ici_sub_Ici' (laplace_linear_tail hrp 0).1 (laplace_linear_tail hrp N).1,
        (laplace_linear_tail hrp 0).2, (laplace_linear_tail hrp N).2]
      simp only [zero_mul, add_zero, neg_zero, Real.exp_zero, mul_one]; ring
    rw [hf]; field_simp; ring

theorem fineAliasLaplaceKernel_measurable (T0 N : ℝ) (hN : T0 ≤ N) :
    Measurable (fineAliasLaplaceKernel T0 N) := by
  unfold fineAliasLaplaceKernel
  simp_rw [intervalIntegral.integral_of_le hN]
  have hm : Measurable fun rt : ℝ × ℝ => rt.2 * Real.exp (-(rt.2*rt.1)) := by fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

def spatialInverseFourConstant (d : ℕ) : ℝ :=
  (d : ℝ) * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) * ((d-5).factorial : ℝ)

theorem fineAlias_spatial_squared_integrable_and_integral_le {d : ℕ} (hd : 4 < d)
    {T0 N : ℝ} (hT0 : 0 < T0) (hN : T0 ≤ N) (x : Covariate d) :
    Integrable (fun y => (fineAliasLaplaceKernel T0 N (exactEuclideanDistance x y))^2) volume ∧
      (∫ y, (fineAliasLaplaceKernel T0 N (exactEuclideanDistance x y))^2) ≤
        6 * spatialInverseFourConstant d / T0^(d-4) := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  have hrad {r : ℝ} (hr : r ≠ 0) : r^(d-1) * (Real.exp (-(T0*r))/r^4) = r^(d-5) * Real.exp (-(T0*r)) := by
    calc _ = (r^(d-1)/r^4) * Real.exp (-(T0*r)) := by ring
      _ = _ := by rw [show d-1 = d-5+4 by omega, pow_add]; field_simp
  have henv : Integrable (fun z : EuclideanSpace ℝ (Fin d) => Real.exp (-(T0*‖z‖))/‖z‖^4) volume := by
    refine (integrable_fun_norm_addHaar volume (f := fun r : ℝ => Real.exp (-(T0*r))/r^4)).2 ?_
    refine ((gamma_monomial_integrable hT0 (d-5)).mono_set Ioi_subset_Ici_self).congr_fun
      (fun r hr => ?_) measurableSet_Ioi
    simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
    exact (hrad hr.ne').symm
  have henv_int : (∫ z : EuclideanSpace ℝ (Fin d), Real.exp (-(T0*‖z‖))/‖z‖^4) =
      spatialInverseFourConstant d / T0^(d-4) := by
    rw [integral_fun_norm_addHaar volume fun r : ℝ => Real.exp (-(T0*r))/r^4]
    simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
    rw [setIntegral_congr_fun (g := fun r => r^(d-5)*Real.exp (-(T0*r))) measurableSet_Ioi
      (fun r hr => hrad hr.ne'), ← integral_Ici_eq_integral_Ioi, gamma_monomial_integral hT0,
      show d-5+1 = d-4 by omega]
    unfold spatialInverseFourConstant; ring
  have hm : Measurable fun z : EuclideanSpace ℝ (Fin d) => (fineAliasLaplaceKernel T0 N ‖z‖)^2 :=
    ((fineAliasLaplaceKernel_measurable T0 N hN).comp continuous_norm.measurable).pow_const 2
  have hb : ∀ᵐ z : EuclideanSpace ℝ (Fin d) ∂volume,
      (fineAliasLaplaceKernel T0 N ‖z‖)^2 ≤ 6 * (Real.exp (-(T0*‖z‖))/‖z‖^4) := by
    filter_upwards [volume.ae_ne (0 : EuclideanSpace ℝ (Fin d))] with z hz
    have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hw0 : 0 ≤ fineAliasLaplaceKernel T0 N ‖z‖ :=
      intervalIntegral.integral_nonneg hN fun T hT => mul_nonneg (hT0.le.trans hT.1) (Real.exp_pos _).le
    have hw2 : fineAliasLaplaceKernel T0 N ‖z‖ ≤ (1+T0*‖z‖)*Real.exp (-(T0*‖z‖))/‖z‖^2 := by
      unfold fineAliasLaplaceKernel
      rw [← intervalIntegral.integral_Ici_sub_Ici' (laplace_linear_tail hr T0).1 (laplace_linear_tail hr N).1,
        (laplace_linear_tail hr T0).2, (laplace_linear_tail hr N).2]
      have hn0 := hT0.le.trans hN
      exact sub_le_self _ (div_nonneg (by positivity) (sq_nonneg _))
    have hp := pair_defect_exponential_absorption (T0*‖z‖) (mul_nonneg hT0.le hr.le)
    calc
      _ ≤ ((1+T0*‖z‖)*Real.exp (-(T0*‖z‖))/‖z‖^2)^2 := pow_le_pow_left₀ hw0 hw2 2
      _ = (1+T0*‖z‖)^2 * Real.exp (-(2*T0*‖z‖)) / ‖z‖^4 := by
        rw [div_pow, mul_pow, ← Real.exp_nat_mul, show (‖z‖^2)^2 = ‖z‖^4 by ring,
          show ((2 : ℕ) : ℝ) * -(T0*‖z‖) = -(2*T0*‖z‖) by ring]
      _ ≤ 6 * Real.exp (-(T0*‖z‖)) / ‖z‖^4 :=
        div_le_div_of_nonneg_right (by simpa only [mul_assoc] using hp) (by positivity)
      _ = _ := by ring
  have hiE : Integrable (fun z : EuclideanSpace ℝ (Fin d) => (fineAliasLaplaceKernel T0 N ‖z‖)^2) volume :=
    (henv.const_mul 6).mono' hm.aestronglyMeasurable <| hb.mono fun z hz => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hz
  have hleE : (∫ z : EuclideanSpace ℝ (Fin d), (fineAliasLaplaceKernel T0 N ‖z‖)^2) ≤
      6 * spatialInverseFourConstant d / T0^(d-4) :=
    (integral_mono_ae hiE (henv.const_mul 6) hb).trans_eq (by rw [integral_const_mul, henv_int]; ring)
  rw [← (PiLp.volume_preserving_toLp (Fin d)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 _).measurableEmbedding] at hiE
  have hi0 : Integrable (fun z : Covariate d => (fineAliasLaplaceKernel T0 N ‖WithLp.toLp 2 z‖)^2) volume := by
    simpa only [Function.comp_def] using hiE
  refine ⟨by simpa only [exactEuclideanDistance_eq_norm] using hi0.comp_sub_right x, ?_⟩
  simp_rw [exactEuclideanDistance_eq_norm]
  rw [integral_sub_right_eq_self (μ := volume) fun z : Covariate d => (fineAliasLaplaceKernel T0 N ‖WithLp.toLp 2 z‖)^2]
  exact ((PiLp.volume_preserving_toLp (Fin d)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding
    fun z : EuclideanSpace ℝ (Fin d) => (fineAliasLaplaceKernel T0 N ‖z‖)^2).trans_le hleE

theorem spatialPi_const_smul {J E : Type*} [Fintype J] [MeasurableSpace E]
    (π : Measure E) [SigmaFinite π] (c : ℝ≥0∞) [SigmaFinite (c • π)] :
    Measure.pi (fun _ : J => c • π) = c^(Fintype.card J) • Measure.pi (fun _ : J => π) := by
  classical
  apply Measure.pi_eq (μ := fun _ : J => c • π); intro S _
  rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

def spatialPatchProbability (d : ℕ) : Measure (Covariate d) :=
  ((2 : ℝ≥0∞)^d)⁻¹ • volume.restrict (spatialPatchBox d)

instance spatialPatchProbability_isProbability (d : ℕ) : IsProbabilityMeasure (spatialPatchProbability d) :=
  ⟨by rw [spatialPatchProbability, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ, spatialPatchBox_volume]
      exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)⟩

theorem spatialPatchProbability_le_volume (d : ℕ) : spatialPatchProbability d ≤ volume := by
  have hc : ((2 : ℝ≥0∞)^d)⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr (one_le_pow₀ (by norm_num))
  intro S
  rw [spatialPatchProbability, Measure.smul_apply, smul_eq_mul]
  exact (mul_le_of_le_one_left zero_le hc).trans (Measure.restrict_le_self S)

theorem spatial_probability_pair_exponential_integral_le {d : ℕ} (hd : 0 < d)
    (π : Measure (Covariate d)) [IsProbabilityMeasure π] (hπ : π ≤ volume)
    {T : ℝ} (hT : 0 < T) :
    (∫ xy : Covariate d × Covariate d, Real.exp (-(T * exactEuclideanDistance xy.1 xy.2)) ∂π.prod π) ≤
      spatialExponentialConstant d / T^d := by
  have hm : Measurable fun xy : Covariate d × Covariate d =>
      Real.exp (-(T * exactEuclideanDistance xy.1 xy.2)) :=
    (exactEuclideanDistance_continuous (d := d) |>.const_mul T |>.neg |>.rexp).measurable
  have hi : Integrable (fun xy : Covariate d × Covariate d =>
      Real.exp (-(T * exactEuclideanDistance xy.1 xy.2))) (π.prod π) :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun _ => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hT.le (exactEuclideanDistance_nonneg _ _))))
  rw [integral_prod _ hi]
  simpa only [integral_const, probReal_univ, one_smul] using
    integral_mono hi.integral_prod_left (integrable_const (spatialExponentialConstant d / T^d)) fun x =>
      (integral_mono_measure hπ (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
        (exactEuclideanDistance_exponential_integrable_and_integral hd hT x).1).trans_eq
          (exactEuclideanDistance_exponential_integrable_and_integral hd hT x).2

theorem spatialPi_two_pairs_integral_factor {J : Type*} [Fintype J]
    {d : ℕ} (π : Measure (Covariate d)) [IsProbabilityMeasure π]
    (q : Fin 4 ↪ J) (T : ℝ) :
    (∫ U : J → Covariate d,
      Real.exp (-(T * (exactEuclideanDistance (U (q 0)) (U (q 1)) +
        exactEuclideanDistance (U (q 2)) (U (q 3))))) ∂Measure.pi fun _ : J => π) =
      (∫ xy : Covariate d × Covariate d, Real.exp (-(T * exactEuclideanDistance xy.1 xy.2)) ∂π.prod π)^2 := by
  classical
  let F (xy : Covariate d × Covariate d) := Real.exp (-(T * exactEuclideanDistance xy.1 xy.2))
  have hF : Measurable F := (exactEuclideanDistance_continuous (d := d) |>.const_mul T |>.neg |>.rexp).measurable
  have hc : iIndepFun (fun j (U : J → Covariate d) => U j) (Measure.pi fun _ : J => π) :=
    iIndepFun_pi (X := fun _ : J => (id : Covariate d → Covariate d)) fun _ => aemeasurable_id
  have hpair (i j : J) (hij : i ≠ j) :
      (∫ U : J → Covariate d, F (U i, U j) ∂Measure.pi fun _ : J => π) = ∫ z, F z ∂π.prod π := by
    let e : Fin 2 ↪ J := ⟨![i, j], fun a b h => by fin_cases a <;> fin_cases b <;> simp_all⟩
    have hproj : MeasurePreserving (fun U : J → Covariate d => fun l => U (e l))
        (Measure.pi fun _ : J => π) (Measure.pi fun _ : Fin 2 => π) :=
      ⟨measurable_pi_iff.mpr fun l => measurable_pi_apply (e l), by
        simpa only [(measurePreserving_eval (fun _ : J => π) _).map_eq] using
          (iIndepFun_iff_map_fun_eq_pi_map fun l => (measurable_pi_apply (e l)).aemeasurable).mp
            (iIndepFun.precomp e.injective hc)⟩
    have hp : MeasurePreserving (fun U : J → Covariate d => (U i, U j)) (Measure.pi fun _ : J => π) (π.prod π) := by
      convert (measurePreserving_finTwoArrow π).comp hproj using 1
      funext U; simp [MeasurableEquiv.finTwoArrow, e]
    exact (integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable).symm.trans
      (congrArg (fun μ => ∫ z, F z ∂μ) hp.map_eq)
  have hne (i j : Fin 4) (h : i ≠ j) : q i ≠ q j := fun he => h (q.injective he)
  have hind := (hc.indepFun_prodMk_prodMk (fun j => measurable_pi_apply j)
    (q 0) (q 1) (q 2) (q 3) (hne 0 2 (by decide)) (hne 0 3 (by decide))
    (hne 1 2 (by decide)) (hne 1 3 (by decide))).comp hF hF
  have he := hind.integral_mul_eq_mul_integral
    (hF.comp ((measurable_pi_apply (q 0)).prodMk (measurable_pi_apply (q 1)))).aestronglyMeasurable
    (hF.comp ((measurable_pi_apply (q 2)).prodMk (measurable_pi_apply (q 3)))).aestronglyMeasurable
  change (∫ U : J → Covariate d, F (U (q 0), U (q 1)) * F (U (q 2), U (q 3)) ∂Measure.pi fun _ : J => π) = _ at he
  simp only [Function.comp_def] at he
  rw [hpair (q 0) (q 1) (hne 0 1 (by decide)), hpair (q 2) (q 3) (hne 2 3 (by decide)), ← sq] at he
  simpa only [F, ← Real.exp_add, show ∀ a b : ℝ, -(T*a) + -(T*b) = -(T*(a+b)) by intros; ring] using he

theorem finite_pi_subset_integrable {I E : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace E] (μ : Measure E) [IsFiniteMeasure μ]
    (s : Finset I) (f : (s → E) → ℝ) (hf : Integrable f (Measure.pi fun _ : s => μ)) :
    Integrable (fun U : I → E => f fun j : s => U j.val) (Measure.pi fun _ : I => μ) := by
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : I => μ) fun i => i ∈ s
  rw [show (@Measure.pi s (fun _ => E) (Subtype.fintype fun i => i ∈ s) (fun _ => inferInstance) fun _ => μ) =
    Measure.pi fun _ : s => μ by congr 1; exact Subsingleton.elim _ _] at hp
  exact hp.integrable_comp_of_integrable (hf.comp_fst _)

def spatialSubsetConfiguration {d k : ℕ} (s : Finset (Fin k))
    (U : Fin k → Covariate d) : Fin s.card → Covariate d :=
  fun j => U ((Fintype.equivFin s).symm (Fin.cast (Fintype.card_coe s).symm j)).val

theorem spatialSubsetConfiguration_measurable {d k : ℕ} (s : Finset (Fin k)) :
    Measurable (spatialSubsetConfiguration (d := d) s) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

theorem finite_pi_reindex_integral {I J E : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] (e : I ≃ J) (f : (J → E) → ℝ) :
    (∫ U : I → E, f (fun j => U (e.symm j)) ∂Measure.pi fun _ : I => μ) =
      ∫ V, f V ∂Measure.pi fun _ : J => μ := by
  have h := (measurePreserving_piCongrLeft (fun _ : J => μ) e).integral_comp' f
  simp only [MeasurableEquiv.coe_piCongrLeft] at h
  simpa only [show ∀ U : I → E, (Equiv.piCongrLeft (fun _ : J => E) e) U = fun j => U (e.symm j) from
    fun U => funext fun _ => by simp only [Equiv.piCongrLeft_apply_eq_cast, cast_eq]] using h

theorem spatial_subset_square_integral_enumerated {d k : ℕ} (s : Finset (Fin k))
    (f : (Fin s.card → Covariate d) → ℝ) :
    (∫ U : Fin k → Covariate d, f (spatialSubsetConfiguration s U) ^ 2
      ∂fullSpatialPatchDesign d k) = (2 : ℝ) ^ (d * (k - s.card)) *
        ∫ V, f V ^ 2 ∂fullSpatialPatchDesign d s.card := by
  let μ := volume.restrict (spatialPatchBox d)
  let e : s ≃ Fin s.card := (Fintype.equivFin s).trans (finCongr (Fintype.card_coe s))
  let g (V : s → Covariate d) := f (fun j => V (e.symm j)) ^ 2
  let eqv := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin k => Covariate d) fun i => i ∈ s
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin k => μ) fun i => i ∈ s
  rw [show (@Measure.pi s (fun _ => Covariate d) (Subtype.fintype fun i => i ∈ s) (fun _ => inferInstance) fun _ => μ) =
    Measure.pi fun _ : s => μ by congr 1; exact Subsingleton.elim _ _] at hp
  have hsub : (∫ U : Fin k → Covariate d, g (fun j : s => U j.val) ∂fullSpatialPatchDesign d k) =
      (2 : ℝ) ^ (d * (k - s.card)) * ∫ V, g V ∂Measure.pi fun _ : s => μ := by
    have h := hp.symm.integral_comp' fun U : Fin k → Covariate d => g fun j : s => U j.val
    change (∫ z : (s → Covariate d) × ({i : Fin k // i ∉ s} → Covariate d), g (fun j : s => eqv.symm z j.val)
      ∂(Measure.pi fun _ : s => μ).prod (Measure.pi fun _ : {i : Fin k // i ∉ s} => μ)) = _ at h
    simp_rw [show ∀ z : (s → Covariate d) × ({i : Fin k // i ∉ s} → Covariate d),
      (fun j : s => eqv.symm z j.val) = z.1 from fun z => funext fun j => by
        change (if h : j.val ∈ s then z.1 ⟨j.val, h⟩ else z.2 ⟨j.val, h⟩) = z.1 j; simp [j.property]] at h
    rw [fullSpatialPatchDesign, ← h, integral_fun_fst]
    simp only [μ, measureReal_def, Measure.pi_univ, Measure.restrict_apply_univ,
      Finset.prod_const, Finset.card_univ, ENNReal.toReal_pow,
      Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, smul_eq_mul]
    change (volume.real (spatialPatchBox d)) ^ (k - s.card) * _ = _
    rw [spatialPatchBox_real_volume, ← pow_mul]
  change (∫ U : Fin k → Covariate d, g (fun j : s => U j.val) ∂fullSpatialPatchDesign d k) = _
  rw [hsub, finite_pi_reindex_integral μ e fun V => f V ^ 2]; rfl

end SpatialKernelsAndProducts

-- ============================================================================
-- 2. Local Frame, Fine-Pair Matrices & Hyperplane Packet, and Score Bounds
-- ============================================================================

section FrameAndFinePairScore
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def highChartLift (k : ℕ) (j : ZMod k) (x : ℝ) : ℤ :=
  (j.val : ℤ) + (k : ℤ) * Int.floor (x - (j.val : ℝ) / k + 1 / 2)

theorem highChartLift_eq_of_close (k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : ZMod k) (x : ℝ) (z : ℤ) (hz : (z : ZMod k) = j)
    (hclose : |(k : ℝ) * x - z| < 1) : highChartLift k j x = z := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_iff k z j).mp hz
  have htR : (z : ℝ) = (j.val : ℝ) + (k : ℝ) * t := by exact_mod_cast ht
  have harg : (k : ℝ) * (x - (j.val : ℝ) / k + 1/2) = (k : ℝ) * x - j.val + k/2 := by field_simp
  have hbounds := abs_lt.mp hclose
  have hf : Int.floor (x - (j.val : ℝ) / k + 1/2) = t :=
    Int.floor_eq_iff.mpr ⟨(mul_le_mul_iff_right₀ hkR).mp (by nlinarith),
      (mul_lt_mul_iff_right₀ hkR).mp (by nlinarith)⟩
  simp only [highChartLift, hf]; exact ht.symm

def highRawChartCoordinate (k : ℕ) (j : ZMod k) (x : ℝ) : ℝ :=
  (k : ℝ) * x - highChartLift k j x

def highLocalCoordinate (k : ℕ) (j : ZMod k) (x : ℝ) : ℝ :=
  if |highRawChartCoordinate k j x| ≤ 1 then highRawChartCoordinate k j x else 0

def highLocalCoordinates (d k : ℕ) (j : HighWindowLabels d k) (x : Covariate d) : Covariate d :=
  fun r => highLocalCoordinate k (j r) (x r)

theorem highLocalCoordinates_measurable (d k : ℕ) (j : HighWindowLabels d k) :
    Measurable (highLocalCoordinates d k j) := by
  refine measurable_pi_iff.mpr fun r => (?_ : Measurable (highLocalCoordinate k (j r))).comp (measurable_pi_apply r)
  have hraw : Measurable (highRawChartCoordinate k (j r)) :=
    (measurable_const.mul measurable_id).sub
      ((measurable_of_countable fun z : ℤ => (z : ℝ)).comp
        (measurable_const.add (measurable_const.mul (Int.measurable_floor.comp (by fun_prop)))))
  exact Measurable.ite (measurableSet_le hraw.abs measurable_const) hraw measurable_const

theorem highLocalCoordinates_abs_le_one (d k : ℕ) (j : HighWindowLabels d k)
    (x : Covariate d) (r : Fin d) : |highLocalCoordinates d k j x r| ≤ 1 := by
  unfold highLocalCoordinates highLocalCoordinate
  split_ifs with h
  · exact h
  · norm_num

def highLocalFrameFeature {d D : ℕ} (k : ℕ) (j : HighWindowLabels d k)
    (x : Covariate d) (γ : HighFrameIndex d D) : ℝ :=
  highFrameFeature (highLocalCoordinates d k j x) γ

theorem highLocalFrameFeature_measurable {d D : ℕ} (k : ℕ)
    (j : HighWindowLabels d k) (γ : HighFrameIndex d D) :
    Measurable fun x => highLocalFrameFeature k j x γ := by
  unfold highLocalFrameFeature highFrameFeature
  exact Finset.measurable_fun_prod _ fun r _ =>
    (((measurable_pi_apply r).comp (highLocalCoordinates_measurable d k j)).div_const 8).pow_const _

def highLocalFieldWithout (d k D : ℕ) [NeZero k] (η : ℝ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ) (j : HighWindowLabels d k)
    (x : Covariate d) : ℝ :=
  η * ∑ l ∈ (Finset.univ : Finset (HighWindowLabels d k)).erase j,
    highPeriodizedChart d k l (highFrameProfile (highFramePolynomial (c l))) x

section LocalFrameDecomp
attribute [local instance] Classical.propDecidable

theorem highFrameField_local_decomposition (d k D : ℕ) [NeZero k] (hk : 4 ≤ k)
    (η : ℝ) (c : HighWindowLabels d k → HighFrameIndex d D → ℝ)
    (j : HighWindowLabels d k) (x : Covariate d) :
    highFrameField d k η (fun l => highFramePolynomial (c l)) x =
      highLocalFieldWithout d k D η c j x + η * highPeriodicTensor d k j x *
        ∑ γ, highLocalFrameFeature k j x γ * c j γ := by
  let raw (u : Covariate d) : Covariate d := fun r => highRawChartCoordinate k (j r) (u r)
  have hwin (j₀ : ZMod k) (x₀ : ℝ) :
      highPeriodicWindow k j₀ x₀ = highWindowProfile ((k : ℝ) * x₀ - highChartLift k j₀ x₀) := by
    unfold highPeriodicWindow
    have hres : (highChartLift k j₀ x₀ : ZMod k) = j₀ := by simp [highChartLift]
    rw [finsum_eq_single _ (highChartLift k j₀ x₀)]
    · simp only [ite_eq_left hres]
    · intro z hz
      by_cases hj : (z : ZMod k) = j₀
      · simp only [ite_eq_left hj]
        by_contra hp
        have hc : |(k : ℝ) * x₀ - z| < 3/4 := by
          by_contra h; exact hp (highWindowProfile_eq_zero _ (not_lt.mp h))
        exact hz (highChartLift_eq_of_close k hk j₀ x₀ z hj (by linarith)).symm
      · simp only [ite_eq_right hj]
  have hpt : highPeriodicTensor d k j x = highWindowTensor d (raw x) := by
    unfold highPeriodicTensor highWindowTensor raw highRawChartCoordinate
    simp_rw [hwin]
  have hmon (γ : HighFrameIndex d D) :
      highPeriodizedChart d k j (highFrameProfile (highFrameMonomial γ)) x =
        highPeriodicTensor d k j x * highLocalFrameFeature k j x γ := by
    have hG0 := highFrameProfile_zero_of_window_zero (highFrameMonomial γ)
    have hchart : highPeriodizedChart d k j (highFrameProfile (highFrameMonomial γ)) x =
        highFrameProfile (highFrameMonomial γ) (raw x) := by
      unfold highPeriodizedChart
      rw [finsum_eq_single _ fun r => highChartLift k (j r) (x r)]
      · have hres : ∀ r, (highChartLift k (j r) (x r) : ZMod k) = j r := fun r => by simp [highChartLift]
        simp only [hres, implies_true, ite_true]; rfl
      · intro z hz
        by_cases hres : ∀ r, (z r : ZMod k) = j r
        · simp only [ite_eq_left hres]
          by_contra hG
          have hprof : highWindowTensor d (fun r => (k : ℝ) * x r - z r) ≠ 0 := fun hp => hG (hG0 _ hp)
          refine hz (funext fun r => ?_)
          have hpr : highWindowProfile ((k : ℝ) * x r - z r) ≠ 0 :=
            fun hp => hprof (Finset.prod_eq_zero (Finset.mem_univ r) hp)
          have hc : |(k : ℝ) * x r - z r| < 3/4 := by
            by_contra hp; exact hpr (highWindowProfile_eq_zero _ (not_lt.mp hp))
          exact (highChartLift_eq_of_close k hk (j r) (x r) (z r) (hres r) (by linarith)).symm
        · simp only [ite_eq_right hres]
    rw [hchart]; unfold highFrameProfile
    rw [frameScaledPolynomial_eval]
    have hmev : MvPolynomial.eval (fun i => raw x i / 8) (highFrameMonomial γ) = highFrameFeature (raw x) γ := by
      unfold highFrameMonomial highFrameFeature
      rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_fintype _ _ fun _ => pow_zero _]
      simp only [polynomial_box_exponent_apply]
    rw [hmev, ← hpt]
    by_cases hw : highPeriodicTensor d k j x = 0
    · simp only [hw, zero_mul]
    · congr 1; unfold highLocalFrameFeature; congr 1
      funext r; dsimp only [highLocalCoordinates, highLocalCoordinate, raw]
      rw [hpt] at hw
      have hp : highWindowProfile (raw x r) ≠ 0 := fun hp => hw (Finset.prod_eq_zero (Finset.mem_univ r) hp)
      have hc : |highRawChartCoordinate k (j r) (x r)| < 3/4 := by
        by_contra h; exact hp (highWindowProfile_eq_zero _ (not_lt.mp h))
      simp only [if_pos (by linarith : |highRawChartCoordinate k (j r) (x r)| ≤ 1)]
  have hpoly : highPeriodizedChart d k j (highFrameProfile (highFramePolynomial (c j))) x =
      highPeriodicTensor d k j x * ∑ γ, highLocalFrameFeature k j x γ * c j γ := by
    rw [highPeriodizedFrame_evaluation, Finset.mul_sum]
    exact Finset.sum_congr rfl fun γ _ => by rw [hmon γ]; ring
  have hs := Finset.sum_erase_add (Finset.univ : Finset (HighWindowLabels d k))
    (fun l => highPeriodizedChart d k l (highFrameProfile (highFramePolynomial (c l))) x)
    (Finset.mem_univ j)
  rw [hpoly] at hs
  unfold highFrameField highLocalFieldWithout; rw [← hs]; ring

end LocalFrameDecomp

theorem highFrameField_coefficientRegression (d k D n : ℕ) [NeZero k] (hk : 4 ≤ k)
    (η : ℝ) (c : HighWindowLabels d k → HighFrameIndex d D → ℝ)
    (j : HighWindowLabels d k) (x : Fin n → Covariate d) :
    coefficientRegression η (fun i => highLocalFieldWithout d k D η c j (x i))
      (fun i => highPeriodicTensor d k j (x i))
      (fun i => highLocalFrameFeature k j (x i)) (c j) =
      fun i => highFrameField d k η (fun l => highFramePolynomial (c l)) (x i) :=
  funext fun i => (highFrameField_local_decomposition d k D hk η c j (x i)).symm

theorem highLocalFieldWithout_continuous (d k D : ℕ) [NeZero k] (η : ℝ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ) (j : HighWindowLabels d k) :
    Continuous (highLocalFieldWithout d k D η c j) :=
  Continuous.const_mul (continuous_finsetSum _ fun l _ =>
    (highPeriodizedChart_contDiff d k l _
      (highFrameProfile_contDiff (highFramePolynomial (c l)))
      (highFrameProfile_zero_of_window_zero (highFramePolynomial (c l)))).continuous) _

theorem highLocalFrameFeature_ball_abs_le_one {d D : ℕ} (k : ℕ)
    (j : HighWindowLabels d k) (x : Covariate d) (C : ℝ) (hC : 1 ≤ C)
    (c : HighFrameIndex d D → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹) :
    |∑ γ, highLocalFrameFeature k j x γ * c γ| ≤ 1 := by
  refine ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun γ _ => ?_)).trans
    (hc.trans ((inv_le_one₀ (by linarith : 0 < C)).mpr hC))
  rw [abs_mul]
  refine (mul_le_mul_of_nonneg_right ?_ (abs_nonneg (c γ))).trans_eq (one_mul _)
  unfold highLocalFrameFeature highFrameFeature; rw [Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun r _ => ?_
  rw [abs_pow]
  refine pow_le_one₀ (abs_nonneg _) ?_
  rw [abs_div]; norm_num; linarith [highLocalCoordinates_abs_le_one d k j x r]

section FinePairMatrices
open MvPolynomial

def finePairCoordinatePolynomial {d : ℕ} (l : Fin d) : MvPolynomial (Fin d) ℝ := C 8 * X l
def finePairSquarePolynomial (d : ℕ) : MvPolynomial (Fin d) ℝ :=
  ∑ l, (finePairCoordinatePolynomial l) ^ 2

def finePairUnitMatrix (d F : ℕ) (β β' : HighFrameIndex d F) : ℝ :=
  highFrameCoefficients (1 : MvPolynomial (Fin d) ℝ) β * highFrameCoefficients 1 β'

def finePairDistanceMatrix (d F : ℕ) (β β' : HighFrameIndex d F) : ℝ :=
  (∑ l : Fin d, 2 * highFrameCoefficients (finePairCoordinatePolynomial l) β *
    highFrameCoefficients (finePairCoordinatePolynomial l) β') -
    highFrameCoefficients (finePairSquarePolynomial d) β * highFrameCoefficients 1 β' -
    highFrameCoefficients (1 : MvPolynomial (Fin d) ℝ) β *
      highFrameCoefficients (finePairSquarePolynomial d) β'

theorem finePairUnitMatrix_symmetric (d F : ℕ) (β β' : HighFrameIndex d F) :
    finePairUnitMatrix d F β β' = finePairUnitMatrix d F β' β := mul_comm _ _

lemma spatial_frame_covariance_outer {κ : Type*} [Fintype κ] [DecidableEq κ]
    {n : ℕ} (u v : κ → ℝ) (φ : Fin n → κ → ℝ) (i j : Fin n) :
    spatialFrameCovariance (fun β β' => u β * v β') φ i j =
      (∑ β, φ i β * u β) * (∑ β, φ j β * v β) := by
  simp only [spatialFrameCovariance, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem finePairUnitMatrix_kernel {d n F : ℕ} (U : Fin n → Covariate d) (i j : Fin n) :
    spatialFrameCovariance (finePairUnitMatrix d F) (fun l => highFrameFeature (U l)) i j = 1 := by
  unfold finePairUnitMatrix; rw [spatial_frame_covariance_outer]
  have he (x : Covariate d) : (∑ β : HighFrameIndex d F,
      highFrameFeature x β * highFrameCoefficients (1 : MvPolynomial (Fin d) ℝ) β) = 1 := by
    simpa only [map_one] using (high_frame_polynomial_evaluation (1 : MvPolynomial (Fin d) ℝ) (by simp) x).symm
  rw [he, he, one_mul]

lemma finePairDistanceMatrix_kernel {d n F : ℕ} (hF : 3 ≤ F)
    (U : Fin n → Covariate d) (i j : Fin n) :
    spatialFrameCovariance (finePairDistanceMatrix d F) (fun l => highFrameFeature (U l)) i j =
      -spatialSquaredDistance (U i) (U j) := by
  have hc (x : Covariate d) : (∑ β : HighFrameIndex d F,
      highFrameFeature x β * highFrameCoefficients (1 : MvPolynomial (Fin d) ℝ) β) = 1 := by
    simpa only [map_one] using (high_frame_polynomial_evaluation (1 : MvPolynomial (Fin d) ℝ) (by simp) x).symm
  have hdeg1 (l : Fin d) : (finePairCoordinatePolynomial l).totalDegree ≤ 1 :=
    (totalDegree_mul _ _).trans (by simp [finePairCoordinatePolynomial])
  have hl (x : Covariate d) (l : Fin d) : (∑ β : HighFrameIndex d F,
      highFrameFeature x β * highFrameCoefficients (finePairCoordinatePolynomial l) β) = x l :=
    (high_frame_polynomial_evaluation (finePairCoordinatePolynomial l)
      ((hdeg1 l).trans (by omega)) x).symm.trans
      (by simp only [finePairCoordinatePolynomial, map_mul, eval_C, eval_X]; ring)
  have hdeg2 : (finePairSquarePolynomial d).totalDegree ≤ 2 :=
    (totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ =>
      (totalDegree_pow _ _).trans (by nlinarith only [hdeg1 l]))
  have hs (x : Covariate d) : (∑ β : HighFrameIndex d F,
      highFrameFeature x β * highFrameCoefficients (finePairSquarePolynomial d) β) = ∑ l, (x l) ^ 2 :=
    (high_frame_polynomial_evaluation (finePairSquarePolynomial d)
      (hdeg2.trans (by omega)) x).symm.trans
      (by simp only [finePairSquarePolynomial, map_sum, map_pow, finePairCoordinatePolynomial, map_mul, eval_C, eval_X]
          exact Finset.sum_congr rfl fun _ _ => by ring)
  have hsub {A B : HighFrameIndex d F → HighFrameIndex d F → ℝ} :
      spatialFrameCovariance (fun β β' => A β β' - B β β') (fun l => highFrameFeature (U l)) i j =
        spatialFrameCovariance A (fun l => highFrameFeature (U l)) i j -
          spatialFrameCovariance B (fun l => highFrameFeature (U l)) i j := by
    simp only [spatialFrameCovariance, mul_sub, Finset.sum_sub_distrib]
  unfold finePairDistanceMatrix
  rw [hsub, hsub, spatial_frame_covariance_sum]
  simp_rw [spatial_frame_covariance_rank_one, spatial_frame_covariance_outer, hc, hl, hs]
  simp only [mul_one, one_mul, spatialSquaredDistance, Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

def finePairCombinedMatrix (d F : ℕ) (W : ℝ) (β β' : HighFrameIndex d F) : ℝ :=
  finePairUnitMatrix d F β β' + W * finePairDistanceMatrix d F β β'

lemma finePairResponseCountTwo_numerator {d F : ℕ} (hF : 3 ≤ F)
    (q : ℕ) (hq : 2 ≤ q) (C a V η W : ℝ) (hC : C ≠ 0)
    (U : Fin 2 → Covariate d) (p g w : Fin 2 → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin 2 → Fin 3) :
    (p 0 * p 1) * responseMatrixAction q C (finePairCombinedMatrix d F W) c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) -
      η ^ 2 * (p 0 * p 1) * ∑ i, (w i) ^ 2 *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i =
      η ^ 2 * w 0 * w 1 * p 0 * p 1 *
        (1 - W * spatialSquaredDistance (U 0) (U 1)) *
        ternaryMeanDerivative a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c 0) (y 0) *
        ternaryMeanDerivative a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c 1) (y 1) := by
  let A := finePairCombinedMatrix d F W
  have hsym (β β') : A β β' = A β' β := by
    dsimp [A, finePairCombinedMatrix, finePairUnitMatrix, finePairDistanceMatrix]
    rw [show (∑ l : Fin d, 2 * highFrameCoefficients (finePairCoordinatePolynomial l) β *
        highFrameCoefficients (finePairCoordinatePolynomial l) β') =
      ∑ l : Fin d, 2 * highFrameCoefficients (finePairCoordinatePolynomial l) β' *
        highFrameCoefficients (finePairCoordinatePolynomial l) β from Finset.sum_congr rfl fun _ _ => by ring]
    ring
  let δ := coefficientDirection η w (fun i => highFrameFeature (U i)) c
  let f := coefficientRegression η g w (fun i => highFrameFeature (U i)) c
  let m := fun i => ternaryMeanDerivative a (f i) (y i)
  let e := fun i => highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i
  have he0 : ({0, 1} : Finset (Fin 2)).erase 0 = {1} := by decide
  have he1 : ({0, 1} : Finset (Fin 2)).erase 1 = {0} := by decide
  have hs (v : HighFrameIndex d F → ℝ) : finiteProductSecond Finset.univ
      (fun i z => ternaryMass a (f i + z * δ v i) V (y i))
      (fun i z => δ v i * ternaryMeanDerivative a (f i + z * δ v i) (y i))
      (fun i _ => (δ v i) ^ 2 * ternaryMeanSecondDerivative a (y i)) 0 =
      (2 * e 0) * (δ v 0 * δ v 0) + (2 * e 1) * (δ v 1 * δ v 1) +
        (2 * m 0 * m 1) * (δ v 0 * δ v 1) := by
    simp [finiteProductSecond, Finset.univ_fin2, he0, he1, e, highResponseVarianceTerm,
      ternary_heat_identity, m, f]; ring
  have htwo : responseMatrixAction q C A c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) =
      η ^ 2 * (w 0) ^ 2 * spatialFrameCovariance A (fun i => highFrameFeature (U i)) 0 0 * e 0 +
      η ^ 2 * (w 1) ^ 2 * spatialFrameCovariance A (fun i => highFrameFeature (U i)) 1 1 * e 1 +
      η ^ 2 * w 0 * w 1 * spatialFrameCovariance A (fun i => highFrameFeature (U i)) 0 1 * m 0 * m 1 := by
    rw [high_response_matrix_second q hq C a V η A g w (fun i => highFrameFeature (U i)) c y]
    change (1 / 2 : ℝ) * covarianceAction C A
      (fun v => finiteProductSecond Finset.univ
        (fun i z => ternaryMass a (f i + z * δ v i) V (y i))
        (fun i z => δ v i * ternaryMeanDerivative a (f i + z * δ v i) (y i))
        (fun i _ => (δ v i) ^ 2 * ternaryMeanSecondDerivative a (y i)) 0) = _
    simp_rw [hs]; rw [covarianceAction_add, covarianceAction_add]; simp_rw [covarianceAction_mul]
    rw [covariance_direction_product C η A hC hsym w _ c 0 0,
      covariance_direction_product C η A hC hsym w _ c 1 1,
      covariance_direction_product C η A hC hsym w _ c 0 1]
    dsimp [m, f, e]; ring
  have hker (i j : Fin 2) : spatialFrameCovariance A (fun l => highFrameFeature (U l)) i j =
      1 - W * spatialSquaredDistance (U i) (U j) := by
    change spatialFrameCovariance (fun β β' => finePairUnitMatrix d F β β' + W * finePairDistanceMatrix d F β β')
      (fun l => highFrameFeature (U l)) i j = _
    rw [spatial_frame_covariance_add,
      show spatialFrameCovariance (fun β β' => W * finePairDistanceMatrix d F β β')
        (fun l => highFrameFeature (U l)) i j =
        W * spatialFrameCovariance (finePairDistanceMatrix d F) (fun l => highFrameFeature (U l)) i j by
          simp only [spatialFrameCovariance, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring,
      finePairUnitMatrix_kernel, finePairDistanceMatrix_kernel hF]
    ring
  rw [htwo, Fin.sum_univ_two]
  simp only [hker, spatialSquaredDistance, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Finset.sum_const_zero, mul_zero, sub_zero, mul_one, e, m, f]
  ring

theorem finePairUnitMatrix_l1_le (d F : ℕ) :
    spatialMatrixL1 (finePairUnitMatrix d F) ≤ 1 := by
  have hu : (∑ β : HighFrameIndex d F, |highFrameCoefficients (1 : MvPolynomial (Fin d) ℝ) β|) ≤ 1 :=
    (highFrameCoefficients_sum_abs_le _).trans_eq frameCoefficientL1_one
  unfold finePairUnitMatrix spatialMatrixL1
  simp only [abs_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  simpa only [one_mul] using mul_le_mul hu hu (Finset.sum_nonneg fun _ _ => abs_nonneg _) zero_le_one

theorem finePairDistanceMatrix_l1_le (d F : ℕ) :
    spatialMatrixL1 (finePairDistanceMatrix d F) ≤ 256 * d := by
  have h0 : (∑ β : HighFrameIndex d F, |highFrameCoefficients (1 : MvPolynomial (Fin d) ℝ) β|) ≤ 1 :=
    (highFrameCoefficients_sum_abs_le _).trans_eq frameCoefficientL1_one
  have hl (l : Fin d) : (∑ β : HighFrameIndex d F, |highFrameCoefficients (finePairCoordinatePolynomial l) β|) ≤ 8 := by
    refine (highFrameCoefficients_sum_abs_le _).trans ?_
    rw [show finePairCoordinatePolynomial l = monomial (Finsupp.single l 1) 8 from C_mul_X_eq_monomial]
    simp [frameCoefficientL1, MvPolynomial.support_monomial]
  have hs : (∑ β : HighFrameIndex d F, |highFrameCoefficients (finePairSquarePolynomial d) β|) ≤ 64 * d := by
    refine (highFrameCoefficients_sum_abs_le _).trans ?_
    rw [show finePairSquarePolynomial d = ∑ l : Fin d, monomial (Finsupp.single l 1 + Finsupp.single l 1) (64 : ℝ) by
      unfold finePairSquarePolynomial
      simp only [show ∀ l : Fin d, finePairCoordinatePolynomial l = monomial (Finsupp.single l 1) 8 from
        fun _ => C_mul_X_eq_monomial, pow_two, monomial_mul]; norm_num]
    refine (frameCoefficientL1_sum_monomial_le _ _).trans_eq ?_
    simp only [show |(64 : ℝ)| = 64 by norm_num, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hsub {A B : HighFrameIndex d F → HighFrameIndex d F → ℝ} :
      spatialMatrixL1 (fun β β' => A β β' - B β β') ≤ spatialMatrixL1 A + spatialMatrixL1 B := by
    simp only [spatialMatrixL1, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => abs_sub _ _
  have hout {u v : HighFrameIndex d F → ℝ} :
      spatialMatrixL1 (fun β β' => u β * v β') = (∑ β, |u β|) * (∑ β, |v β|) := by
    simp only [spatialMatrixL1, abs_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  let B (β β' : HighFrameIndex d F) : ℝ := ∑ l : Fin d, 2 * highFrameCoefficients (finePairCoordinatePolynomial l) β *
    highFrameCoefficients (finePairCoordinatePolynomial l) β'
  have hB : spatialMatrixL1 B ≤ 128 * d := by
    calc
      spatialMatrixL1 B
        ≤ ∑ β : HighFrameIndex d F, ∑ β' : HighFrameIndex d F, ∑ l : Fin d,
            |2 * highFrameCoefficients (finePairCoordinatePolynomial l) β *
              highFrameCoefficients (finePairCoordinatePolynomial l) β'| :=
          Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l : Fin d, ∑ β : HighFrameIndex d F, ∑ β' : HighFrameIndex d F,
            (2 : ℝ) * (|highFrameCoefficients (finePairCoordinatePolynomial l) β| *
              |highFrameCoefficients (finePairCoordinatePolynomial l) β'|) := by
          conv_lhs =>
            arg 2; ext β; rw [Finset.sum_comm]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun β' _ => ?_
          rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num, mul_assoc]
      _ ≤ ∑ _l : Fin d, (128 : ℝ) := by
          refine Finset.sum_le_sum fun l _ => ?_
          simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
          have hh := mul_le_mul (hl l) (hl l) (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)
          linarith
      _ = 128 * d := by simp; ring
  have h1 : spatialMatrixL1 (fun β β' : HighFrameIndex d F => highFrameCoefficients (finePairSquarePolynomial d) β *
      highFrameCoefficients (1 : MvPolynomial (Fin d) ℝ) β') ≤ 64 * d := by
    rw [hout]; exact (mul_le_mul hs h0 (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  have h2 : spatialMatrixL1 (fun β β' : HighFrameIndex d F => highFrameCoefficients (1 : MvPolynomial (Fin d) ℝ) β *
      highFrameCoefficients (finePairSquarePolynomial d) β') ≤ 64 * d := by
    rw [hout, mul_comm]; exact (mul_le_mul hs h0 (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  change spatialMatrixL1 (fun β β' : HighFrameIndex d F => B β β' -
    highFrameCoefficients (finePairSquarePolynomial d) β * highFrameCoefficients 1 β' -
    highFrameCoefficients (1 : MvPolynomial (Fin d) ℝ) β * highFrameCoefficients (finePairSquarePolynomial d) β') ≤ _
  exact ((hsub.trans (add_le_add hsub le_rfl)).trans (add_le_add (add_le_add hB h1) h2)).trans_eq (by ring)

lemma spatial_matrix_l1_eq_zero_iff {d F : ℕ}
    (A : HighFrameIndex d F → HighFrameIndex d F → ℝ) :
    spatialMatrixL1 A = 0 ↔ ∀ β β', A β β' = 0 :=
  ⟨fun h β β' => abs_eq_zero.mp <| le_antisymm
    (((Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ β')).trans
      (Finset.single_le_sum (f := fun β => ∑ γ, |A β γ|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ β))).trans_eq h)
    (abs_nonneg _),
   fun h => by simp [spatialMatrixL1, h]⟩

theorem finePairUnitMatrix_l1_pos (d F : ℕ) :
    0 < spatialMatrixL1 (finePairUnitMatrix d F) := by
  refine lt_of_le_of_ne (spatial_matrix_l1_nonnegative _) fun he => ?_
  have hz := (spatial_matrix_l1_eq_zero_iff _).mp he.symm
  have hk := finePairUnitMatrix_kernel (d := d) (F := F) (n := 1) (fun _ => (0 : Covariate d)) 0 0
  simp only [spatialFrameCovariance, hz, mul_zero, Finset.sum_const_zero] at hk
  norm_num at hk

theorem finePairDistanceMatrix_l1_pos (d F : ℕ) [NeZero d] (hF : 3 ≤ F) :
    0 < spatialMatrixL1 (finePairDistanceMatrix d F) := by
  refine lt_of_le_of_ne (spatial_matrix_l1_nonnegative _) fun he => ?_
  have hz := (spatial_matrix_l1_eq_zero_iff _).mp he.symm
  let U : Fin 2 → Covariate d := fun i _ => if i = 0 then 0 else 1
  have hk := finePairDistanceMatrix_kernel hF U 0 1
  simp only [spatialFrameCovariance, hz, mul_zero, Finset.sum_const_zero] at hk
  have heU : spatialSquaredDistance (U 0) (U 1) = (d : ℝ) := by simp [U, spatialSquaredDistance]
  rw [heU] at hk
  exact NeZero.ne d (Nat.cast_eq_zero.mp (neg_eq_zero.mp hk.symm))

end FinePairMatrices

abbrev FinePairFieldMark (d : ℕ) := partitionFieldMark (Covariate d × ℝ)

theorem boundedHyperplaneFieldValue_section_measurable (d : ℕ) (u : Covariate d) :
    Measurable fun z : FinePairFieldMark d => boundedHyperplaneFieldValue z u :=
  (boundedHyperplaneFieldValue_measurable d).comp (measurable_id.prodMk measurable_const)

def finePairFieldKernel (d : ℕ) : Kernel ℝ (FinePairFieldMark d) where
  toFun := boundedHyperplaneFieldLaw d
  measurable' := boundedHyperplaneFieldLaw_measurable d

instance finePairFieldKernel_markov (d : ℕ) [NeZero d] : IsMarkovKernel (finePairFieldKernel d) :=
  ⟨fun T => boundedHyperplaneFieldLaw_probability d T⟩

def finePairTimeFieldMeasure (d : ℕ) (lo hi : ℝ) : Measure (ℝ × FinePairFieldMark d) :=
  (volume.restrict (Icc lo hi)).compProd (finePairFieldKernel d)

instance finePairTimeFieldMeasure_finite (d : ℕ) [NeZero d] (lo hi : ℝ) :
    IsFiniteMeasure (finePairTimeFieldMeasure d lo hi) := by
  unfold finePairTimeFieldMeasure; infer_instance

theorem finePairTimeFieldMeasure_integral (d : ℕ) [NeZero d] (lo hi : ℝ)
    (f : ℝ × FinePairFieldMark d → ℝ) (hf : Integrable f (finePairTimeFieldMeasure d lo hi)) :
    (∫ e, f e ∂finePairTimeFieldMeasure d lo hi) =
      ∫ T in Icc lo hi, ∫ z, f (T, z) ∂boundedHyperplaneFieldLaw d T :=
  Measure.integral_compProd hf

def finePairTimeFieldValue {d : ℕ} (e : ℝ × FinePairFieldMark d) (u : Covariate d) : ℝ :=
  boundedHyperplaneFieldValue e.2 u

lemma finePairTimeFieldValue_measurable (d : ℕ) :
    Measurable fun ex : (ℝ × FinePairFieldMark d) × Covariate d =>
      finePairTimeFieldValue ex.1 ex.2 :=
  (boundedHyperplaneFieldValue_measurable d).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

theorem finePairTimeFieldValue_abs {d : ℕ} (e : ℝ × FinePairFieldMark d) (u : Covariate d) :
    |finePairTimeFieldValue e u| = 1 := boundedHyperplaneFieldValue_abs _ _

theorem finePairTimeFieldMeasure_fst_integrable (d : ℕ) [NeZero d] (lo hi : ℝ) :
    Integrable (fun e : ℝ × FinePairFieldMark d => e.1) (finePairTimeFieldMeasure d lo hi) := by
  apply (integrable_const (max |lo| |hi|)).mono' measurable_fst.aestronglyMeasurable
  filter_upwards [Measure.ae_compProd_of_ae_fst (finePairFieldKernel d) measurableSet_Icc
    (ae_restrict_mem measurableSet_Icc)] with e he
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [neg_abs_le lo, le_max_left |lo| |hi|, he.1],
    by linarith [le_abs_self hi, le_max_right |lo| |hi|, he.2]⟩

def finePairTimeMatrix {ι : Type*} (d : ℕ) (A : ι → ι → ℝ) (e : ℝ × FinePairFieldMark d) : ι → ι → ℝ :=
  fun i j => e.1 * A i j

theorem finePairTimeMatrix_measurable {ι : Type*} (d : ℕ) (A : ι → ι → ℝ) (i j : ι) :
    Measurable fun e => finePairTimeMatrix d A e i j := measurable_fst.mul_const _

theorem finePairTimeMatrix_cost_integrable {ι : Type*} [Fintype ι]
    (d : ℕ) [NeZero d] (lo hi : ℝ) (A : ι → ι → ℝ) :
    Integrable (separatedMatrixCost (finePairTimeMatrix d A)) (finePairTimeFieldMeasure d lo hi) := by
  have he : separatedMatrixCost (finePairTimeMatrix d A) =
      fun e => |e.1| * (∑ i, ∑ j, |A i j|) := by
    funext e; simp only [separatedMatrixCost, finePairTimeMatrix, abs_mul, Finset.mul_sum]
  rw [he]
  exact (finePairTimeFieldMeasure_fst_integrable d lo hi).abs.mul_const _

lemma finePairTimeMatrix_cost_integral {ι : Type*} [Fintype ι]
    (d : ℕ) [NeZero d] (lo hi : ℝ) (hlo : 0 ≤ lo) (horder : lo ≤ hi) (A : ι → ι → ℝ) :
    (∫ e, separatedMatrixCost (finePairTimeMatrix d A) e ∂finePairTimeFieldMeasure d lo hi) =
      (∑ i, ∑ j, |A i j|) * ((hi ^ 2 - lo ^ 2) / 2) := by
  simp_rw [show ∀ e, separatedMatrixCost (finePairTimeMatrix d A) e = |e.1| * (∑ i, ∑ j, |A i j|) from
    fun _ => by simp only [separatedMatrixCost, finePairTimeMatrix, abs_mul, Finset.mul_sum]]
  rw [integral_mul_const]
  have he : (fun e : ℝ × FinePairFieldMark d => |e.1|) =ᵐ[finePairTimeFieldMeasure d lo hi] fun e => e.1 := by
    filter_upwards [Measure.ae_compProd_of_ae_fst (finePairFieldKernel d) measurableSet_Icc
      (ae_restrict_mem measurableSet_Icc)] with e he
    exact abs_of_nonneg (hlo.trans he.1)
  rw [integral_congr_ae he, finePairTimeFieldMeasure_integral d lo hi _ (finePairTimeFieldMeasure_fst_integrable d lo hi)]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le horder, integral_id, mul_comm]

theorem finePairTimeFieldValue_weighted_covariance (d : ℕ) [NeZero d] (lo hi : ℝ)
    (hlo : 0 ≤ lo) (u v : Covariate d) (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d) :
    (∫ e, e.1 * (finePairTimeFieldValue e u * finePairTimeFieldValue e v)
      ∂finePairTimeFieldMeasure d lo hi) =
      ∫ T in Icc lo hi, T * Real.exp (-T * euclideanNorm fun r => u r - v r) := by
  have hm (w : Covariate d) : Measurable fun e : ℝ × FinePairFieldMark d => finePairTimeFieldValue e w :=
    (boundedHyperplaneFieldValue_section_measurable d w).comp measurable_snd
  have hint : Integrable (fun e => e.1 * (finePairTimeFieldValue e u * finePairTimeFieldValue e v))
      (finePairTimeFieldMeasure d lo hi) :=
    (finePairTimeFieldMeasure_fst_integrable d lo hi).mul_bdd (c := 1)
      ((hm u).mul (hm v)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun e => by
        change ‖finePairTimeFieldValue e u * finePairTimeFieldValue e v‖ ≤ 1
        simp only [Real.norm_eq_abs, abs_mul, finePairTimeFieldValue_abs, one_mul, le_refl])
  rw [finePairTimeFieldMeasure_integral d lo hi _ hint]
  simp only [finePairTimeFieldValue, integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
  rw [boundedHyperplaneField_covariance d T (hlo.trans hT.1) u v hu hv]

def finePairResponseAtomBound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (C : ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) : ℝ :=
  ∑ h : HighResponseMarkIndex ι q,
    |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)|

theorem finePairResponseAtomBound_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (C : ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ)
    (h : HighResponseMarkIndex ι q) :
    |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)| ≤
      finePairResponseAtomBound q C c Φ :=
  Finset.single_le_sum
    (f := fun h : HighResponseMarkIndex ι q =>
      |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ h)

theorem ordinaryPairReset_measurable {Z : Type*} [MeasurableSpace Z] {n : ℕ} (a b : ℝ) (p : Fin n → ℝ)
    (ψ : Z → Fin n → ℝ) (hψ : ∀ i, Measurable fun ζ => ψ ζ i)
    (z : ℝ) (eps : Fin 2 → ℝ) (i : Fin n) :
    Measurable fun ζ => localDensityReset a b 2 z eps p (fun i _ => ψ ζ i) i := by
  unfold localDensityReset
  exact measurable_const.add ((Finset.measurable_fun_sum _ fun l _ => (hψ i).const_mul (eps l)).const_mul _)

theorem ordinaryPairReset_atom_abs_le {n : ℕ} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m D : ℕ) (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc a b)
    (ψ : Fin n → ℝ) (hψ : ∀ i, |ψ i| ≤ 1)
    (e : HighDensityMarkIndex m 2 D) (i : Fin n) :
    |localDensityReset a b 2 (densityPacketAtom a b m 2 D e).1
      (densityPacketAtom a b m 2 D e).2 p (fun i _ => ψ i) i| ≤ b := by
  have hz := densityPacketAtom_mem a b hab.le m 2 D e
  have hh := localDensityReset_mem_interval a b ha hab 2 (by omega) _ hz.1 _ hz.2 p
    (fun i _ => ψ i) i (hp i) fun _ => hψ i
  rw [abs_of_nonneg (ha.le.trans hh.1)]; exact hh.2

theorem responseMatrixAction_matrix_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (C : ℝ) (A B : ι → ι → ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    responseMatrixAction q C (fun i j => A i j + B i j) c Φ =
      responseMatrixAction q C A c Φ + responseMatrixAction q C B c Φ := by
  simp only [responseMatrixAction_entry_sum, add_mul, Finset.sum_add_distrib]

lemma ordinaryPairPacket_pair_action {ι Z : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (m D q : ℕ) (hm : 2 ≤ m) (hD : 2 ≤ D)
    (C : ℝ) (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable fun ζ => A ζ i j)
    (hcost : Integrable (separatedMatrixCost A) σ) (c : ι → ℝ)
    (p : Fin 2 → ℝ) (hp : ∀ i, p i ∈ Icc a b) (ψ : Z → Fin 2 → ℝ)
    (hmψ : ∀ i, Measurable fun ζ => ψ ζ i) (hbψ : ∀ ζ i, |ψ ζ i| ≤ 1)
    (Φ : (ι → ℝ) → ℝ) :
    (∫ᵛ e, highPacketObservable a b m 2 D q C c
      (fun ζ z eps => ∏ i, localDensityReset a b 2 z eps p (fun i _ => ψ ζ i) i) Φ e
      ∂<•highPacketSignedMeasure σ a b m 2 D q C A) =
      (p 0 * p 1) * (∫ ζ, ψ ζ 0 * ψ ζ 1 * responseMatrixAction q C (A ζ) c Φ ∂σ) := by
  classical
  rw [highPacketSignedMeasure_factor_integral σ a b m 2 D q C A hA hcost c
    (fun ζ z eps => ∏ i, localDensityReset a b 2 z eps p (fun i _ => ψ ζ i) i)
    (fun z eps => Finset.measurable_fun_prod _ fun i _ => ordinaryPairReset_measurable a b p ψ hmψ z eps i)
    (b^2) (by positivity)
    (fun ζ e => finite_density_product_abs_bound _ b (ha.trans hab).le
      (ordinaryPairReset_atom_abs_le a b ha hab m D p hp (ψ ζ) (hbψ ζ) e))
    Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)]
  have hact (ζ : Z) : densityPacketAction a b m 2 D
      (fun z eps => ∏ i, localDensityReset a b 2 z eps p (fun i _ => ψ ζ i) i) =
      p 0 * p 1 * ψ ζ 0 * ψ ζ 1 := by
    have hh := density_packet_product_count_selector (Finset.univ : Finset (Fin 2))
      a b ha hab m 2 D (by omega) (by omega) (by simpa using hD) (by simpa using hm) p fun i _ => ψ ζ i
    have hpow : (Finset.univ : Finset (Fin 2)).powersetCard 2 = {Finset.univ} := by
      simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin 2))
    let eqv : Fin 2 ≃ (Finset.univ : Finset (Fin 2)) :=
      (Equiv.subtypeUnivEquiv fun i : Fin 2 => Finset.mem_univ i).symm
    have hsym : densitySeparatedSym 2 (fun i _ => ψ ζ i) Finset.univ = ψ ζ 0 * ψ ζ 1 := by
      rw [densitySeparatedSym_eq_permutation_average 2 _ Finset.univ eqv]
      simp [eqv, Equiv.subtypeUnivEquiv_symm_apply, Fin.prod_univ_two, Fintype.card_perm]
    simpa only [Finset.card_univ, Fintype.card_fin, ite_true, hpow, Finset.sum_singleton,
      Fin.prod_univ_two, hsym, mul_assoc] using hh
  unfold highSeparatedPacketAction
  simp_rw [densityPacketAction_mul_right, hact, show ∀ ζ : Z,
    p 0 * p 1 * ψ ζ 0 * ψ ζ 1 * responseMatrixAction q C (A ζ) c Φ =
    (p 0 * p 1) * (ψ ζ 0 * ψ ζ 1 * responseMatrixAction q C (A ζ) c Φ) from fun _ => by ring]
  exact integral_const_mul _ _

def finePairUnitFirstAction {d F n : ℕ} (ad bd : ℝ) (D q : ℕ) (C : ℝ)
    (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  ∫ᵛ e, highPacketObservable ad bd D 2 D q C c
    (fun _ z eps => ∏ i, localDensityReset ad bd 2 z eps p (fun _ _ => 1) i) Φ e
    ∂<•highPacketSignedMeasure (Measure.dirac ()) ad bd D 2 D q C fun _ => finePairUnitMatrix d F

def finePairCoarseFirstAction {d F n : ℕ} (ad bd T0 : ℝ) (D q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  ∫ᵛ e, highPacketObservable ad bd D 2 D q C c
    (fun ζ z eps => ∏ i, localDensityReset ad bd 2 z eps p
      (fun i _ => finePairTimeFieldValue ζ (U i)) i) Φ e
    ∂<•highPacketSignedMeasure (finePairTimeFieldMeasure d 0 T0) ad bd D 2 D q C
      (finePairTimeMatrix d (finePairDistanceMatrix d F))

def finePairFineFirstAction {d F n : ℕ} (ad bd T0 N : ℝ) (M q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  ∫ᵛ e, finePairPacketObservable ad bd M q C c
    (fun ζ z eps => ∏ i, finePairDensityReset ad bd z eps p
      (fun i => finePairTimeFieldValue ζ (U i)) i) Φ e
    ∂<•finePairPacketSignedMeasure (finePairTimeFieldMeasure d T0 N) ad bd M q C
      (finePairTimeMatrix d (finePairDistanceMatrix d F))

def finePairThreeRowFirstAction {d F n : ℕ} (ad bd T0 N : ℝ) (D M q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  finePairUnitFirstAction ad bd D q C p c Φ + finePairCoarseFirstAction ad bd T0 D q C U p c Φ +
    finePairFineFirstAction ad bd T0 N M q C U p c Φ

lemma finePairThreeRowFirstAction_pair {d F : ℕ} [NeZero d]
    (ad bd T0 N : ℝ) (ha : 0 < ad) (hab : ad < bd) (hT0 : 0 ≤ T0) (hN : T0 ≤ N)
    (D M q : ℕ) (hD : 2 ≤ D) (hM : 2 ≤ M) (C : ℝ)
    (U : Fin 2 → Covariate d) (hU : ∀ i, U i ∈ hyperplaneCube d)
    (p : Fin 2 → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairThreeRowFirstAction ad bd T0 N D M q C U p c Φ =
      (p 0 * p 1) * responseMatrixAction q C
        (finePairCombinedMatrix d F (pairLaplaceKernel N (exactEuclideanDistance (U 0) (U 1)))) c Φ := by
  have htr (lo hi : ℝ) (hlo : 0 ≤ lo) :
      (∫ e, finePairTimeFieldValue e (U 0) * finePairTimeFieldValue e (U 1) *
        responseMatrixAction q C (finePairTimeMatrix d (finePairDistanceMatrix d F) e) c Φ
        ∂finePairTimeFieldMeasure d lo hi) =
      (∫ T in Icc lo hi, T * Real.exp (-T * euclideanNorm fun r => U 0 r - U 1 r)) *
        responseMatrixAction q C (finePairDistanceMatrix d F) c Φ := by
    change (∫ e, finePairTimeFieldValue e (U 0) * finePairTimeFieldValue e (U 1) *
      responseMatrixAction q C (fun i j => e.1 * finePairDistanceMatrix d F i j) c Φ
      ∂finePairTimeFieldMeasure d lo hi) = _
    simp_rw [responseMatrixAction_scalar_matrix, show ∀ e : ℝ × FinePairFieldMark d,
      finePairTimeFieldValue e (U 0) * finePairTimeFieldValue e (U 1) *
        (e.1 * responseMatrixAction q C (finePairDistanceMatrix d F) c Φ) =
      (e.1 * (finePairTimeFieldValue e (U 0) * finePairTimeFieldValue e (U 1))) *
        responseMatrixAction q C (finePairDistanceMatrix d F) c Φ from fun _ => by ring]
    rw [integral_mul_const, finePairTimeFieldValue_weighted_covariance d lo hi hlo (U 0) (U 1) (hU 0) (hU 1)]
  have hu1 : finePairUnitFirstAction ad bd D q C p c Φ =
      p 0 * p 1 * responseMatrixAction q C (finePairUnitMatrix d F) c Φ := by
    rw [finePairUnitFirstAction, ordinaryPairPacket_pair_action (Measure.dirac ()) ad bd ha hab D D q hD hD C
      (fun _ => finePairUnitMatrix d F) (fun _ _ => measurable_const) (integrable_const _)
      c p hp (fun _ _ => 1) (fun _ => measurable_const) (by intro _ _; norm_num)]
    simp
  have hc1 : finePairCoarseFirstAction ad bd T0 D q C U p c Φ = (p 0 * p 1) *
      ((∫ T in Icc 0 T0, T * Real.exp (-T * euclideanNorm fun r => U 0 r - U 1 r)) *
        responseMatrixAction q C (finePairDistanceMatrix d F) c Φ) := by
    rw [finePairCoarseFirstAction, ordinaryPairPacket_pair_action (finePairTimeFieldMeasure d 0 T0) ad bd ha hab D D q hD hD C
      (finePairTimeMatrix d (finePairDistanceMatrix d F)) (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 T0 _)
      c p hp (fun ζ i => finePairTimeFieldValue ζ (U i))
      (fun i => (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd)
      (fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le), htr 0 T0 le_rfl]
  have hf1 : finePairFineFirstAction ad bd T0 N M q C U p c Φ = (p 0 * p 1) *
      ((∫ T in Icc T0 N, T * Real.exp (-T * euclideanNorm fun r => U 0 r - U 1 r)) *
        responseMatrixAction q C (finePairDistanceMatrix d F) c Φ) := by
    unfold finePairFineFirstAction; simp only [Fin.prod_univ_two]
    rw [finePairPacketSignedMeasure_pair_action (finePairTimeFieldMeasure d T0 N) ad bd ha hab M q hM C
      (finePairTimeMatrix d (finePairDistanceMatrix d F)) (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T0 N _)
      c p hp (fun ζ i => finePairTimeFieldValue ζ (U i))
      (fun i => (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd)
      (fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le) 0 1
      Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ), htr T0 N hT0]
  rw [finePairThreeRowFirstAction, hu1, hc1, hf1]
  change _ = (p 0 * p 1) * responseMatrixAction q C
    (fun i j => finePairUnitMatrix d F i j +
      pairLaplaceKernel N (exactEuclideanDistance (U 0) (U 1)) * finePairDistanceMatrix d F i j) c Φ
  rw [responseMatrixAction_matrix_add, responseMatrixAction_scalar_matrix, exactEuclideanDistance_eq_euclideanNorm]
  let r0 := euclideanNorm fun r => U 0 r - U 1 r
  have hsplit : (∫ T in Icc 0 T0, T * Real.exp (-(T*r0))) + (∫ T in Icc T0 N, T * Real.exp (-(T*r0))) =
      pairLaplaceKernel N r0 := by
    rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hT0, ← intervalIntegral.integral_of_le hN]
    exact intervalIntegral.integral_add_adjacent_intervals
      (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [show (fun T : ℝ => T * Real.exp (-T * r0)) = fun T => T * Real.exp (-(T * r0)) from
    funext fun _ => by congr 2; ring, ← hsplit]
  ring

theorem finePairThreeRow_count_two_numerator {d F : ℕ} [NeZero d] (hF : 3 ≤ F)
    (ad bd T0 N : ℝ) (ha : 0 < ad) (hab : ad < bd) (hT0 : 0 ≤ T0) (hN : T0 ≤ N)
    (D M q : ℕ) (hD : 2 ≤ D) (hM : 2 ≤ M) (hq : 2 ≤ q)
    (C a V η : ℝ) (hC : C ≠ 0)
    (U : Fin 2 → Covariate d) (hU : ∀ i, U i ∈ hyperplaneCube d)
    (p : Fin 2 → ℝ) (hp : ∀ i, p i ∈ Icc ad bd) (g w : Fin 2 → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin 2 → Fin 3) :
    finePairThreeRowFirstAction ad bd T0 N D M q C U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) -
      η^2 * (p 0 * p 1) * ∑ i, (w i)^2 *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i =
      η^2 * w 0 * w 1 * p 0 * p 1 *
        ((1 + N * exactEuclideanDistance (U 0) (U 1)) *
          Real.exp (-(N * exactEuclideanDistance (U 0) (U 1)))) *
        ternaryMeanDerivative a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c 0) (y 0) *
        ternaryMeanDerivative a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c 1) (y 1) := by
  rw [finePairThreeRowFirstAction_pair ad bd T0 N ha hab hT0 hN D M q hD hM C U hU p hp,
    finePairResponseCountTwo_numerator hF q hq C a V η _ hC U p g w c y]
  have hr : 0 ≤ exactEuclideanDistance (U 0) (U 1) := Real.sqrt_nonneg _
  have hsq : (exactEuclideanDistance (U 0) (U 1))^2 = spatialSquaredDistance (U 0) (U 1) :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [← hsq, mul_comm (pairLaplaceKernel _ _), pairLaplaceKernel_defect N _ hr]

theorem finePairThreeRowFirstAction_small_count {d F n : ℕ} [NeZero d] (hn : n < 2)
    (ad bd T0 N : ℝ) (ha : 0 < ad) (hab : ad < bd) (D M q : ℕ) (hD : 1 ≤ D)
    (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairThreeRowFirstAction ad bd T0 N D M q C U p c Φ = 0 := by
  have hord {Z : Type} [MeasurableSpace Z] (σ : Measure Z) [IsFiniteMeasure σ]
      (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
      (hA : ∀ i j, Measurable fun ζ => A ζ i j) (hcost : Integrable (separatedMatrixCost A) σ)
      (ψ : Z → Fin n → ℝ) (hmψ : ∀ i, Measurable fun ζ => ψ ζ i) (hbψ : ∀ ζ i, |ψ ζ i| ≤ 1) :
      (∫ᵛ e, highPacketObservable ad bd D 2 D q C c
        (fun ζ z eps => ∏ i, localDensityReset ad bd 2 z eps p (fun i _ => ψ ζ i) i) Φ e
        ∂<•highPacketSignedMeasure σ ad bd D 2 D q C A) = 0 := by
    rw [highPacketSignedMeasure_factor_integral σ ad bd D 2 D q C A hA hcost c
      (fun ζ z eps => ∏ i, localDensityReset ad bd 2 z eps p (fun i _ => ψ ζ i) i)
      (fun z eps => Finset.measurable_fun_prod _ fun i _ => ordinaryPairReset_measurable ad bd p ψ hmψ z eps i)
      (bd^n) (pow_nonneg (ha.trans hab).le n)
      (fun ζ e => finite_density_product_abs_bound _ bd (ha.trans hab).le
        (ordinaryPairReset_atom_abs_le ad bd ha hab D D p hp (ψ ζ) (hbψ ζ) e))
      Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)]
    unfold highSeparatedPacketAction
    simp_rw [densityPacketAction_mul_right,
      density_packet_product_zero_of_small_count Finset.univ ad bd ha hab D 2 D
        (by omega) hD (by simpa using (show n ≤ D by omega)) (by simpa using hn) p _, zero_mul]
    exact integral_zero _ _
  have hunit : finePairUnitFirstAction ad bd D q C p c Φ = 0 :=
    hord (Measure.dirac ()) (fun _ => finePairUnitMatrix d F) (fun _ _ => measurable_const)
      (integrable_const _) (fun _ _ => 1) (fun _ => measurable_const) (by intro _ _; norm_num)
  have hcoarse : finePairCoarseFirstAction ad bd T0 D q C U p c Φ = 0 :=
    hord (finePairTimeFieldMeasure d 0 T0) _ (finePairTimeMatrix_measurable d _)
      (finePairTimeMatrix_cost_integrable d 0 T0 _) (fun ζ i => finePairTimeFieldValue ζ (U i))
      (fun i => (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd)
      fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le
  have hfine : finePairFineFirstAction ad bd T0 N M q C U p c Φ = 0 := by
    let ψ (ζ : ℝ × FinePairFieldMark d) (i : Fin n) := finePairTimeFieldValue ζ (U i)
    have hmψ (i : Fin n) : Measurable fun ζ => ψ ζ i :=
      (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd
    rw [finePairFineFirstAction, finePairPacketSignedMeasure_factor_integral _ ad bd M q C _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T0 N _) c
      (fun ζ z eps => ∏ i, finePairDensityReset ad bd z eps p (ψ ζ) i)
      (fun z eps => Finset.measurable_fun_prod _ fun i _ => measurable_const.add ((hmψ i).const_mul _))
      (bd^n) (pow_nonneg (ha.trans hab).le n)
      (fun ζ e => finite_density_product_abs_bound _ bd (ha.trans hab).le fun i =>
        finePairFieldReset_abs_le ad bd ha hab M p hp ψ (fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le) (ζ, e) i)
      Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)]
    have hf0 (ζ) : (∫ᵛ e, (∏ i, finePairDensityReset ad bd e.1 e.2 p (ψ ζ) i) ∂<•finePairDensitySignedRule ad bd M) = 0 := by
      rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
      · simpa only [Finset.univ_eq_empty, Finset.prod_empty] using finePairDensitySignedRule_mass_zero ad bd M
      · simpa only [Fin.prod_univ_one] using finePairDensitySignedRule_linear_zero ad bd M p (ψ ζ) (0 : Fin 1)
    simp_rw [hf0, zero_mul]; exact integral_zero _ _
  simp only [finePairThreeRowFirstAction, hunit, hcoarse, hfine, add_zero]

end FrameAndFinePairScore

-- ============================================================================
-- 3. Union Score, Union Reset, Fine-Pair/Higher-Band Rows, and Union History
-- ============================================================================

section UnionRowsAndHistory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

section MarkedLocalScore
attribute [local instance] Classical.propDecidable
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]

def highMarkedResponseAction {n : ℕ} (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (pReset : E → Fin n → ℝ) (cReset : E → ι → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (y : Fin n → Fin 3) : ℝ :=
  ∫ e, activation e * (∏ i, pReset e i) *
    highResponseProduct a V η g w φ (cReset e) y ∂π

def highMarkedLocalScore {n : ℕ} (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (p : Fin n → ℝ) (pReset : E → Fin n → ℝ)
    (cReset : E → ι → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (c : ι → ℝ) (y : Fin n → Fin 3) : ℝ :=
  (highMarkedResponseAction π activation a V η pReset cReset g w φ y -
    η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i) /
    ((∏ i, p i) * highResponseProduct a V η g w φ c y)

theorem highMarkedResponseProduct_measurable {n : ℕ} (a V η : ℝ)
    (cReset : E → ι → ℝ) (hc : ∀ γ, Measurable fun e => cReset e γ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (y : Fin n → Fin 3) :
    Measurable fun e => highResponseProduct a V η g w φ (cReset e) y := by
  unfold highResponseProduct
  apply Finset.measurable_fun_prod; intro i _
  apply ternaryMass_measurable_comp
  unfold coefficientRegression; fun_prop

theorem highMarkedResponseProduct_abs_le_one {n : ℕ} (a V η : ℝ) (ha : a ≠ 0)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (v : ι → ℝ)
    (hp : ∀ i b, 0 ≤ ternaryMass a (coefficientRegression η g w φ v i) V b)
    (y : Fin n → Fin 3) : |highResponseProduct a V η g w φ v y| ≤ 1 := by
  unfold highResponseProduct; rw [Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => ?_
  rw [abs_of_nonneg (hp i (y i))]
  exact ternary_mass_le_one a _ V ha (hp i) (y i)

theorem highMarkedResponseAction_integrable {n : ℕ} (π : Measure E)
    (activation : E → ℝ) (hAct : Integrable activation π)
    (a V η : ℝ) (ha : a ≠ 0) (pPlus : ℝ) (hpPlus : 0 ≤ pPlus)
    (pReset : E → Fin n → ℝ) (hReset : ∀ i, Measurable fun e => pReset e i)
    (hBound : ∀ e i, |pReset e i| ≤ pPlus) (cReset : E → ι → ℝ)
    (hc : ∀ γ, Measurable fun e => cReset e γ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (hp : ∀ e i b, 0 ≤ ternaryMass a (coefficientRegression η g w φ (cReset e) i) V b)
    (y : Fin n → Fin 3) :
    Integrable (fun e => activation e * (∏ i, pReset e i) *
      highResponseProduct a V η g w φ (cReset e) y) π :=
  (hAct.mul_bdd (Finset.measurable_fun_prod _ fun i _ => hReset i).aestronglyMeasurable
    (Filter.Eventually.of_forall fun e => by
      simpa only [Real.norm_eq_abs] using finite_density_product_abs_bound (pReset e) pPlus hpPlus (hBound e))).mul_bdd
    (highMarkedResponseProduct_measurable a V η cReset hc g w φ y).aestronglyMeasurable
    (Filter.Eventually.of_forall fun e => by
      simpa only [Real.norm_eq_abs] using highMarkedResponseProduct_abs_le_one a V η ha g w φ (cReset e) (hp e) y)

theorem highMarkedLocalScore_centered {n : ℕ} (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (ha : a ≠ 0) (p : Fin n → ℝ) (pReset : E → Fin n → ℝ)
    (cReset : E → ι → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b)
    (hInt : ∀ y, Integrable (fun e => activation e * (∏ i, pReset e i) *
      highResponseProduct a V η g w φ (cReset e) y) π)
    (hDensity : (∫ e, activation e * ∏ i, pReset e i ∂π) = 0) :
    (∫ y, highMarkedLocalScore π activation a V η p pReset cReset g w φ c y
      ∂Measure.pi (fun i => ternaryIndexMeasure a (coefficientRegression η g w φ c i) V
        ha fun b => (hp i b).le)) = 0 := by
  rw [ternary_index_product_integral]
  change (∑ y, highResponseProduct a V η g w φ c y *
    highMarkedLocalScore π activation a V η p pReset cReset g w φ c y) = 0
  have hB : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hpd i
  have he (y : Fin n → Fin 3) :
      highResponseProduct a V η g w φ c y *
        highMarkedLocalScore π activation a V η p pReset cReset g w φ c y =
      (highMarkedResponseAction π activation a V η pReset cReset g w φ y -
        η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i) / (∏ i, p i) := by
    have hL : highResponseProduct a V η g w φ c y ≠ 0 := ne_of_gt (Finset.prod_pos fun i _ => hp i (y i))
    unfold highMarkedLocalScore; field_simp [hB, hL]
  simp_rw [he]
  have hsum : (∑ y : Fin n → Fin 3, highMarkedResponseAction π activation a V η pReset cReset g w φ y) =
      ∫ e, activation e * ∏ i, pReset e i ∂π := by
    unfold highMarkedResponseAction
    rw [← integral_finsetSum Finset.univ fun y _ => hInt y]
    simp_rw [← Finset.mul_sum, high_response_product_normalized a V η ha, mul_one]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, hsum, hDensity, ← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.mul_sum, high_response_variance_term_sum_zero,
    mul_zero, Finset.sum_const_zero, sub_zero, zero_div]

theorem highMarkedLocalScore_depends_on_support {n : ℕ} (π : Measure E)
    (activation : E → ℝ) (a V η : ℝ) (p : Fin n → ℝ) (pReset : E → Fin n → ℝ)
    (cReset : E → ι → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (S : Finset (Fin n)) (hw : ∀ i, i ∉ S → w i = 0)
    (y y' : Fin n → Fin 3) (hyy : ∀ i ∈ S, y i = y' i)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b) :
    highMarkedLocalScore π activation a V η p pReset cReset g w φ c y =
      highMarkedLocalScore π activation a V η p pReset cReset g w φ c y' := by
  have hB : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hpd i
  have hLy : highResponseProduct a V η g w φ c y ≠ 0 := ne_of_gt (Finset.prod_pos fun i _ => hp i (y i))
  have hLy' : highResponseProduct a V η g w φ c y' ≠ 0 := ne_of_gt (Finset.prod_pos fun i _ => hp i (y' i))
  have hfirst : highMarkedResponseAction π activation a V η pReset cReset g w φ y /
      highResponseProduct a V η g w φ c y =
    highMarkedResponseAction π activation a V η pReset cReset g w φ y' /
      highResponseProduct a V η g w φ c y' := by
    unfold highMarkedResponseAction
    rw [← integral_div, ← integral_div]
    refine integral_congr_ae <| Filter.Eventually.of_forall fun e => ?_
    simp only [mul_div_assoc]
    rw [high_response_ratio_depends_on_support a V η g w φ c (cReset e) S hw y y' hyy hp]
  have hvar :
      (∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i) /
        highResponseProduct a V η g w φ c y =
      (∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y' i) /
        highResponseProduct a V η g w φ c y' := by
    simp_rw [Finset.sum_div, mul_div_assoc,
      high_response_variance_ratio a V η g w φ c y _ fun i => hp i (y i),
      high_response_variance_ratio a V η g w φ c y' _ fun i => hp i (y' i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ S
    · rw [hyy i hi]
    · simp [hw i hi]
  have hrep (z : Fin n → Fin 3) (hL : highResponseProduct a V η g w φ c z ≠ 0) :
      highMarkedLocalScore π activation a V η p pReset cReset g w φ c z =
      (highMarkedResponseAction π activation a V η pReset cReset g w φ z /
        highResponseProduct a V η g w φ c z) / (∏ i, p i) -
      η ^ 2 * ((∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c z i) /
        highResponseProduct a V η g w φ c z) := by
    unfold highMarkedLocalScore; field_simp [hB, hL]
  rw [hrep y hLy, hrep y' hLy', hfirst, hvar]

end MarkedLocalScore

structure HighUnionRowData (d k F : ℕ) (I : Type*) (E : I → Type*)
    [∀ i, MeasurableSpace (E i)] where
  rowLaw : (i : I) → Measure (E i)
  rowMass : I → ℝ
  rowActivation : (i : I) → E i → ℝ
  rowIntercept : (i : I) → E i → ℝ
  rowSlope : HighWindowLabels d k → (i : I) → E i → Covariate d → ℝ
  rowVector : (i : I) → E i → HighFrameIndex d F → ℝ
  rowTime : (i : I) → E i → ℝ

abbrev HighUnionMark {I : Type*} (E : I → Type*) := (Sigma E) ⊕ Unit

theorem highUnionMark_standardBorel {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)] :
    StandardBorelSpace (HighUnionMark E) := by
  letI : StandardBorelSpace (Sigma E) := highRowReferenceUnion_standardBorel
  letI := upgradeStandardBorel (Sigma E)
  letI : BorelSpace ((Sigma E) ⊕ Unit) := packetSum_borelSpace
  infer_instance

section UnionReset
attribute [local instance] Classical.propDecidable
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] (R : HighUnionRowData d k F I E)

def highUnionLaw (δ : ℝ) : Measure (HighUnionMark E) :=
  highCenteredRowUnionLaw R.rowLaw R.rowMass δ

def highUnionActivation (δ : ℝ) : HighUnionMark E → ℝ :=
  highCenteredRowUnionActivation R.rowMass R.rowActivation δ

def highUnionIntercept (δ : ℝ) : HighUnionMark E → ℝ :=
  highCenteredRowUnionIntercept R.rowLaw R.rowMass R.rowIntercept δ

def highUnionSlope (j : HighWindowLabels d k) (e : HighUnionMark E) (x : Covariate d) : ℝ :=
  highCenteredRowUnionSlope (fun i e => R.rowSlope j i e x) e

def highUnionResponseVector : HighUnionMark E → HighFrameIndex d F → ℝ :=
  Sum.elim (fun e => R.rowVector e.1 e.2) fun _ => 0

def highUnionResponseTime : HighUnionMark E → ℝ :=
  Sum.elim (fun e => R.rowTime e.1 e.2) fun _ => 0

def highUnionResponseReset (e : HighUnionMark E) (c : HighFrameIndex d F → ℝ) :
    HighFrameIndex d F → ℝ :=
  coefficientReset c (highUnionResponseVector R e) (highUnionResponseTime R e)

def highUnionRawUpdate (δ : ℝ) (j : HighWindowLabels d k) (e : HighUnionMark E)
    (θ : HighRawState d k F) : HighRawState d k F :=
  rawPatchUpdate j (highTorusPatch d k j) (highUnionSlope R j e)
    (fun _ => highUnionIntercept R δ e) (highUnionResponseReset R e) θ

theorem highUnionLaw_probability [∀ i, IsProbabilityMeasure (R.rowLaw i)]
    (hMass : ∀ i, 0 ≤ R.rowMass i) (hTotal : 0 < highRowTotalMass R.rowMass)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) : IsProbabilityMeasure (highUnionLaw R δ) :=
  highCenteredRowUnionLaw_probability R.rowLaw R.rowMass hMass hTotal δ hδ0 hδ1

theorem highUnionActivation_measurable (hAct : ∀ i, Measurable (R.rowActivation i)) (δ : ℝ) :
    Measurable (highUnionActivation R δ) :=
  highCenteredRowUnionActivation_measurable R.rowMass R.rowActivation hAct δ

theorem highUnionActivation_centered (hMass : ∀ i, 0 ≤ R.rowMass i)
    (hAct : ∀ i, Measurable (R.rowActivation i))
    (hiAct : ∀ i, Integrable (R.rowActivation i) (R.rowLaw i))
    (hcAct : ∀ i, (∫ e, R.rowActivation i e ∂(R.rowLaw i)) = 0)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫ e, highUnionActivation R δ e ∂highUnionLaw R δ) = 0 :=
  highCenteredRowUnionActivation_centered R.rowLaw R.rowMass hMass R.rowActivation
    hAct hiAct hcAct δ hδ hδ1

lemma highUnionIntercept_measurable (hOffset : ∀ i, Measurable (R.rowIntercept i)) (δ : ℝ) :
    Measurable (highUnionIntercept R δ) :=
  highCenteredRowUnionIntercept_measurable R.rowLaw R.rowMass R.rowIntercept hOffset δ

theorem highUnionSlope_joint_measurable [∀ i, StandardBorelSpace (E i)]
    (hSlope : ∀ j i, Measurable fun ex : E i × Covariate d => R.rowSlope j i ex.1 ex.2)
    (j : HighWindowLabels d k) :
    Measurable fun ex : HighUnionMark E × Covariate d => highUnionSlope R j ex.1 ex.2 := by
  let G : Sigma (fun i => E i × Covariate d) → ℝ := fun ex => R.rowSlope j ex.1 ex.2.1 ex.2.2
  have hSigma : Measurable fun ex : (Sigma E) × Covariate d => R.rowSlope j ex.1.1 ex.1.2 ex.2 :=
    ((historySigma_measurable_iff G).mpr (hSlope j)).comp
      (historySigmaProdMeasurableEquiv E (Covariate d)).measurable
  convert (hSigma.sumElim (measurable_const (a := (0 : ℝ)))).comp
    (MeasurableEquiv.sumProdDistrib (Sigma E) Unit (Covariate d)).measurable using 1
  funext ⟨e, _⟩; cases e <;> rfl

theorem highUnionResponseVector_measurable
    (hVector : ∀ i γ, Measurable fun e => R.rowVector i e γ) (γ : HighFrameIndex d F) :
    Measurable fun e => highUnionResponseVector R e γ :=
  (rowSigmaFunction_measurable (fun i e => R.rowVector i e γ) fun i => hVector i γ).sumElim measurable_const

theorem highUnionResponseTime_measurable (hTime : ∀ i, Measurable (R.rowTime i)) :
    Measurable (highUnionResponseTime R) :=
  (rowSigmaFunction_measurable R.rowTime hTime).sumElim measurable_const

theorem highUnionRawUpdate_measurable [∀ i, StandardBorelSpace (E i)]
    (hSlope : ∀ j i, Measurable fun ex : E i × Covariate d => R.rowSlope j i ex.1 ex.2)
    (hOffset : ∀ i, Measurable (R.rowIntercept i))
    (hVector : ∀ i γ, Measurable fun e => R.rowVector i e γ)
    (hTime : ∀ i, Measurable (R.rowTime i)) (δ : ℝ) (j : HighWindowLabels d k) :
    Measurable fun eθ : HighUnionMark E × HighRawState d k F =>
      highUnionRawUpdate R δ j eθ.1 eθ.2 := by
  have hs (x : Covariate d) : Measurable fun e => highUnionSlope R j e x :=
    (highUnionSlope_joint_measurable R hSlope j).comp (measurable_id.prodMk measurable_const)
  refine Measurable.prodMk (measurable_pi_iff.mpr fun x => ?_)
    (measurable_pi_iff.mpr fun l => measurable_pi_iff.mpr fun γ => ?_)
  · by_cases hx : x ∈ highTorusPatch d k j
    · simp only [highUnionRawUpdate, rawPatchUpdate, affinePatchUpdate, if_pos hx]
      exact ((hs x).comp measurable_fst).mul
        ((measurable_pi_apply x).comp (measurable_fst.comp measurable_snd)) |>.add
        ((highUnionIntercept_measurable R hOffset δ).comp measurable_fst)
    · simp only [highUnionRawUpdate, rawPatchUpdate, affinePatchUpdate, if_neg hx]
      exact (measurable_pi_apply x).comp (measurable_fst.comp measurable_snd)
  · by_cases hl : l = j
    · subst l
      simp only [highUnionRawUpdate, rawPatchUpdate, responseCoordinateUpdate,
        Function.update_self, highUnionResponseReset, coefficientReset]
      exact ((measurable_const.sub ((highUnionResponseTime_measurable R hTime).comp
          measurable_fst)).mul (by fun_prop)).add
        (((highUnionResponseTime_measurable R hTime).comp measurable_fst).mul
          ((highUnionResponseVector_measurable R hVector γ).comp measurable_fst))
    · simp only [highUnionRawUpdate, rawPatchUpdate, responseCoordinateUpdate, Function.update_of_ne hl]
      fun_prop

theorem highUnionResponseReset_ball (Cfr : ℝ) (hCfr : 0 < Cfr)
    (hVector : ∀ i e, (∑ γ, |R.rowVector i e γ|) ≤ Cfr⁻¹)
    (hTime : ∀ i e, R.rowTime i e ∈ Icc (0 : ℝ) 1)
    (e : HighUnionMark E) (c : HighFrameIndex d F → ℝ)
    (hc : (∑ γ, |c γ|) ≤ Cfr⁻¹) :
    (∑ γ, |highUnionResponseReset R e c γ|) ≤ Cfr⁻¹ :=
  coefficientReset_mem_ball Cfr c _ _
    (by cases e with | inl e => exact hTime e.1 e.2 | inr _ => simp [highUnionResponseTime]) hc
    (by cases e with | inl e => exact hVector e.1 e.2 | inr _ => simp [highUnionResponseVector, hCfr.le])

end UnionReset

inductive FinePairRowTag where
  | unit | coarse | fine
  deriving DecidableEq, Fintype

def FinePairRowMark (d D M q : ℕ) : FinePairRowTag → Type
  | .unit => Unit × HighPacketMarkIndex (HighFrameIndex d D) D 2 D q
  | .coarse => (ℝ × FinePairFieldMark d) × HighPacketMarkIndex (HighFrameIndex d D) D 2 D q
  | .fine => (ℝ × FinePairFieldMark d) × FinePairPacketIndex (HighFrameIndex d D) M q

instance finePairRowMark_measurable (d D M q : ℕ) (i : FinePairRowTag) :
    MeasurableSpace (FinePairRowMark d D M q i) := by
  cases i <;> dsimp [FinePairRowMark] <;> infer_instance

instance finePairRowMark_standardBorel (d D M q : ℕ) (i : FinePairRowTag) :
    StandardBorelSpace (FinePairRowMark d D M q i) := by
  letI : StandardBorelSpace (ℝ × FinePairFieldMark d) := by infer_instance
  letI : StandardBorelSpace (HighPacketMarkIndex (HighFrameIndex d D) D 2 D q) := by infer_instance
  letI : StandardBorelSpace (FinePairPacketIndex (HighFrameIndex d D) M q) := by infer_instance
  cases i <;> dsimp [FinePairRowMark, finePairRowMark_measurable] <;> infer_instance

def finePairRowLaw (d D M q : ℕ) (a b C T₀ N : ℝ) :
    (i : FinePairRowTag) → Measure (FinePairRowMark d D M q i)
  | .unit => highPacketAbsoluteLaw (Measure.dirac ()) a b D 2 D q C fun _ => finePairUnitMatrix d D
  | .coarse => highPacketAbsoluteLaw (finePairTimeFieldMeasure d 0 T₀) a b D 2 D q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))
  | .fine => finePairPacketAbsoluteLaw (finePairTimeFieldMeasure d T₀ N) a b M q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))

def finePairRowMass (d D M q : ℕ) (a b C T₀ N : ℝ) : FinePairRowTag → ℝ
  | .unit => highPacketMarkMass (Measure.dirac ()) a b D 2 D q C fun _ => finePairUnitMatrix d D
  | .coarse => highPacketMarkMass (finePairTimeFieldMeasure d 0 T₀) a b D 2 D q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))
  | .fine => finePairPacketMarkMass (finePairTimeFieldMeasure d T₀ N) a b M q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))

def finePairRowActivation (d D M q : ℕ) (a b C T₀ N : ℝ) :
    (i : FinePairRowTag) → FinePairRowMark d D M q i → ℝ
  | .unit => highPacketActivation (Measure.dirac ()) a b D 2 D q C fun _ => finePairUnitMatrix d D
  | .coarse => highPacketActivation (finePairTimeFieldMeasure d 0 T₀) a b D 2 D q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))
  | .fine => finePairPacketActivation (finePairTimeFieldMeasure d T₀ N) a b M q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))

def finePairRowIntercept (d D M q : ℕ) (a b : ℝ) :
    (i : FinePairRowTag) → FinePairRowMark d D M q i → ℝ
  | .unit => highPacketIntercept a b D 2 D q
  | .coarse => highPacketIntercept a b D 2 D q
  | .fine => finePairPacketIntercept a b M q

def finePairRowSlope (d k D M q : ℕ) (a b : ℝ) (j : HighWindowLabels d k) :
    (i : FinePairRowTag) → FinePairRowMark d D M q i → Covariate d → ℝ
  | .unit => fun e _ => highPacketSlope a b D 2 D q (fun _ _ => 1) e
  | .coarse => fun e x => highPacketSlope a b D 2 D q
      (fun ζ _ => finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) e
  | .fine => fun e x => finePairPacketSlope a b M q
      (fun ζ => finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) e

def finePairRowVector (d D M q : ℕ) (C : ℝ) :
    (i : FinePairRowTag) → FinePairRowMark d D M q i → HighFrameIndex d D → ℝ
  | .unit => fun e => (highResponseMarkAtom C q e.2.2).2
  | .coarse => fun e => (highResponseMarkAtom C q e.2.2).2
  | .fine => finePairPacketResponseVector M q C

def finePairRowTime (d D M q : ℕ) :
    (i : FinePairRowTag) → FinePairRowMark d D M q i → ℝ
  | .unit => fun e => (highResponseMarkAtom 0 q e.2.2).1
  | .coarse => fun e => (highResponseMarkAtom 0 q e.2.2).1
  | .fine => finePairPacketResponseTime M q

def finePairRowData (d k D M q : ℕ) (a b C T₀ N : ℝ) :
    HighUnionRowData d k D FinePairRowTag (FinePairRowMark d D M q) where
  rowLaw := finePairRowLaw d D M q a b C T₀ N
  rowMass := finePairRowMass d D M q a b C T₀ N
  rowActivation := finePairRowActivation d D M q a b C T₀ N
  rowIntercept := finePairRowIntercept d D M q a b
  rowSlope := finePairRowSlope d k D M q a b
  rowVector := finePairRowVector d D M q C
  rowTime := finePairRowTime d D M q

theorem finePairRowMass_nonneg (d D M q : ℕ) (a b C T₀ N : ℝ) (i : FinePairRowTag) :
    0 ≤ finePairRowMass d D M q a b C T₀ N i := by
  cases i <;> exact signedMarkMass_nonneg _ _

theorem finePairRowActivation_bound (d D M q : ℕ) (a b C T₀ N : ℝ)
    (i : FinePairRowTag) (e : FinePairRowMark d D M q i) :
    |finePairRowActivation d D M q a b C T₀ N i e| ≤ finePairRowMass d D M q a b C T₀ N i := by
  cases i <;> exact absoluteActivation_bound _ _ _

theorem finePairRowIntercept_mem (d D M q : ℕ) (a b : ℝ) (hab : a ≤ b)
    (i : FinePairRowTag) (e : FinePairRowMark d D M q i) :
    finePairRowIntercept d D M q a b i e ∈ Icc a b := by
  cases i
  · exact (densityPacketAtom_mem a b hab D 2 D e.2.1).1
  · exact (densityPacketAtom_mem a b hab D 2 D e.2.1).1
  · exact finePairPacketIntercept_mem a b hab M q e

theorem finePairRowVector_ball (d D M q : ℕ) (C : ℝ) (hC : 0 < C)
    (i : FinePairRowTag) (e : FinePairRowMark d D M q i) :
    (∑ γ, |finePairRowVector d D M q C i e γ|) ≤ C⁻¹ := by
  cases i <;> exact covarianceAtom_mem_ball C hC _ _ _ _

theorem finePairRowTime_unit (d D M q : ℕ) (i : FinePairRowTag)
    (e : FinePairRowMark d D M q i) : finePairRowTime d D M q i e ∈ Icc (0 : ℝ) 1 := by
  cases i <;> exact responseNode_mem_unit q _

theorem finePairRowIntercept_measurable (d D M q : ℕ) (a b : ℝ) (i : FinePairRowTag) :
    Measurable (finePairRowIntercept d D M q a b i) := by
  cases i
  · exact highPacketIntercept_measurable a b D 2 D q
  · exact highPacketIntercept_measurable a b D 2 D q
  · exact finePairPacketIntercept_measurable a b M q

theorem finePairRowVector_measurable (d D M q : ℕ) (C : ℝ) (i : FinePairRowTag)
    (γ : HighFrameIndex d D) : Measurable fun e => finePairRowVector d D M q C i e γ := by
  cases i
  · exact (measurable_of_countable fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
      (highResponseMarkAtom C q h.2).2 γ).comp measurable_snd
  · exact (measurable_of_countable fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
      (highResponseMarkAtom C q h.2).2 γ).comp measurable_snd
  · exact (measurable_of_countable fun h : FinePairPacketIndex (HighFrameIndex d D) M q =>
      (highResponseMarkAtom C q h.2).2 γ).comp measurable_snd

theorem finePairRowTime_measurable (d D M q : ℕ) (i : FinePairRowTag) :
    Measurable (finePairRowTime d D M q i) := by
  cases i
  · exact (measurable_of_countable fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
      (highResponseMarkAtom 0 q h.2).1).comp measurable_snd
  · exact (measurable_of_countable fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
      (highResponseMarkAtom 0 q h.2).1).comp measurable_snd
  · exact (measurable_of_countable fun h : FinePairPacketIndex (HighFrameIndex d D) M q =>
      (highResponseMarkAtom 0 q h.2).1).comp measurable_snd

theorem finePairRowSlope_joint_measurable (d k D M q : ℕ) (a b : ℝ)
    (j : HighWindowLabels d k) (i : FinePairRowTag) :
    Measurable fun ex : FinePairRowMark d D M q i × Covariate d =>
      finePairRowSlope d k D M q a b j i ex.1 ex.2 := by
  have hψ : Measurable fun zx : (ℝ × FinePairFieldMark d) × Covariate d =>
      finePairTimeFieldValue zx.1 (highLocalCoordinates d k j zx.2) :=
    (finePairTimeFieldValue_measurable d).comp
      (measurable_fst.prodMk ((highLocalCoordinates_measurable d k j).comp measurable_snd))
  cases i
  · exact (highPacketSlope_measurable a b D 2 D q (fun _ : Unit => fun _ => (1 : ℝ))
      fun _ => measurable_const).comp measurable_fst
  · exact ((measurable_of_countable fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
        densityMargin a b (densityPacketAtom a b D 2 D h.1).1 / (2 * b)).comp
          (measurable_snd.comp measurable_fst)).mul
      (Finset.measurable_fun_sum _ fun l _ =>
        ((measurable_of_countable fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
          (densityPacketAtom a b D 2 D h.1).2 l).comp (measurable_snd.comp measurable_fst)).mul
          (hψ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  · exact finePairPacketSlope_joint_measurable a b M q
      (fun ζ x => finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) hψ

theorem finePairRow_reset_interval (d k D M q : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (j : HighWindowLabels d k) (i : FinePairRowTag) (e : FinePairRowMark d D M q i)
    (x : Covariate d) (v : ℝ) (hv : v ∈ Icc a b) :
    finePairRowSlope d k D M q a b j i e x * v + finePairRowIntercept d D M q a b i e ∈ Icc a b := by
  cases i
  · have h := localDensityReset_mem_interval a b ha hab 2 (by norm_num)
      (densityPacketAtom a b D 2 D e.2.1).1 (densityPacketAtom_mem a b hab.le D 2 D e.2.1).1
      (densityPacketAtom a b D 2 D e.2.1).2 (densityPacketAtom_mem a b hab.le D 2 D e.2.1).2
      (fun _ : Unit => v) (fun _ _ => 1) () hv (by intro _; norm_num)
    convert h using 1 <;> dsimp [finePairRowSlope, finePairRowIntercept, highPacketSlope,
      highPacketIntercept, localDensityReset] <;> ring
  · have h := localDensityReset_mem_interval a b ha hab 2 (by norm_num)
      (densityPacketAtom a b D 2 D e.2.1).1 (densityPacketAtom_mem a b hab.le D 2 D e.2.1).1
      (densityPacketAtom a b D 2 D e.2.1).2 (densityPacketAtom_mem a b hab.le D 2 D e.2.1).2
      (fun _ : Unit => v) (fun _ _ => finePairTimeFieldValue e.1 (highLocalCoordinates d k j x))
      () hv fun _ => (finePairTimeFieldValue_abs e.1 _).le
    convert h using 1 <;> dsimp [finePairRowSlope, finePairRowIntercept, highPacketSlope,
      highPacketIntercept, localDensityReset] <;> ring
  · have h := finePairDensityReset_mem_interval a b ha hab _ _
      (finePairPacketIntercept_mem a b hab.le M q e) (fineModulationNode_bound e.2.1.2)
      (fun _ : Unit => v) (fun _ => finePairTimeFieldValue e.1 (highLocalCoordinates d k j x)) () hv
      (finePairTimeFieldValue_abs e.1 _).le
    convert h using 1 <;> dsimp [finePairRowSlope, finePairRowIntercept, finePairPacketSlope,
      finePairPacketIntercept, finePairDensityReset, finePairDensityAtom] <;> ring

section FinePairRowRef
variable (d : ℕ) [NeZero d] (k D M q : ℕ) (a b C T₀ N : ℝ)
    (hpos : ∀ i, 0 < finePairRowMass d D M q a b C T₀ N i)
include hpos

theorem finePairRowLaw_probability (i : FinePairRowTag) :
    IsProbabilityMeasure (finePairRowLaw d D M q a b C T₀ N i) := by
  cases i
  · exact highPacketAbsoluteLaw_probability (Measure.dirac ()) a b D 2 D q C (fun _ => finePairUnitMatrix d D)
      (fun _ _ => measurable_const) (integrable_const _) (hpos .unit)
  · exact highPacketAbsoluteLaw_probability (finePairTimeFieldMeasure d 0 T₀) a b D 2 D q C _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 T₀ _) (hpos .coarse)
  · exact finePairPacketAbsoluteLaw_probability (finePairTimeFieldMeasure d T₀ N) a b M q C _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T₀ N _) (hpos .fine)

theorem finePairRowActivation_measurable (i : FinePairRowTag) :
    Measurable (finePairRowActivation d D M q a b C T₀ N i) := by
  cases i
  · exact absoluteActivation_measurable _ _ (highPacketMarkWeight_measurable a b D 2 D q C _ fun _ _ => measurable_const)
  · exact absoluteActivation_measurable _ _ (highPacketMarkWeight_measurable a b D 2 D q C _ (finePairTimeMatrix_measurable d _))
  · exact absoluteActivation_measurable _ _ (finePairPacketWeight_measurable a b M q C _ (finePairTimeMatrix_measurable d _))

theorem finePairRowActivation_centered (i : FinePairRowTag) :
    (∫ e, finePairRowActivation d D M q a b C T₀ N i e ∂finePairRowLaw d D M q a b C T₀ N i) = 0 := by
  cases i
  · exact highPacketActivation_centered (Measure.dirac ()) a b D 2 D q C (fun _ => finePairUnitMatrix d D)
      (fun _ _ => measurable_const) (integrable_const _) (hpos .unit)
  · exact highPacketActivation_centered (finePairTimeFieldMeasure d 0 T₀) a b D 2 D q C _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 T₀ _) (hpos .coarse)
  · exact finePairPacketActivation_centered (finePairTimeFieldMeasure d T₀ N) a b M q C _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T₀ N _) (hpos .fine)

theorem finePairRowSlope_integrable (ha : 0 < a) (hab : a < b)
    (j : HighWindowLabels d k) (x : Covariate d) (i : FinePairRowTag) :
    Integrable (fun e => finePairRowSlope d k D M q a b j i e x)
      (finePairRowLaw d D M q a b C T₀ N i) := by
  letI := finePairRowLaw_probability d D M q a b C T₀ N hpos i
  apply (integrable_const ((b-a)/(4*b))).mono'
    ((finePairRowSlope_joint_measurable d k D M q a b j i).comp
      (measurable_id.prodMk (measurable_const (a := x)))).aestronglyMeasurable
  refine Filter.Eventually.of_forall fun e => ?_
  rw [Real.norm_eq_abs]
  cases i
  · exact highPacketSlope_bound a b ha hab D 2 D q (by norm_num)
      (fun _ : Unit => fun _ : Fin 2 => (1 : ℝ)) (by intro _ _; norm_num) e
  · exact highPacketSlope_bound a b ha hab D 2 D q (by norm_num) _
      (fun ζ _ => (finePairTimeFieldValue_abs ζ _).le) e
  · exact finePairPacketSlope_bound a b ha hab M q _
      (fun ζ => (finePairTimeFieldValue_abs ζ _).le) e

theorem finePairRowSlope_centered (ha : 0 < a) (hab : a < b)
    (j : HighWindowLabels d k) (x : Covariate d) (i : FinePairRowTag) :
    (∫ e, finePairRowSlope d k D M q a b j i e x ∂finePairRowLaw d D M q a b C T₀ N i) = 0 := by
  have hm : Measurable fun ζ : ℝ × FinePairFieldMark d =>
      finePairTimeFieldValue ζ (highLocalCoordinates d k j x) :=
    (boundedHyperplaneFieldValue_section_measurable d _).comp measurable_snd
  cases i
  · exact highPacketAbsoluteLaw_slope_integral_zero (Measure.dirac ()) a b ha hab D 2 D q (by norm_num)
      C (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _) (hpos .unit)
      (fun _ : Unit => fun _ => 1) (fun _ => measurable_const) (by intro _ _; norm_num)
  · exact highPacketAbsoluteLaw_slope_integral_zero (finePairTimeFieldMeasure d 0 T₀) a b ha hab
      D 2 D q (by norm_num) C _ (finePairTimeMatrix_measurable d _)
      (finePairTimeMatrix_cost_integrable d 0 T₀ _) (hpos .coarse)
      (fun ζ _ => finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) (fun _ => hm)
      fun ζ _ => (finePairTimeFieldValue_abs ζ _).le
  · exact finePairPacketAbsoluteLaw_slope_integral_zero (finePairTimeFieldMeasure d T₀ N) a b M q
      C _ (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T₀ N _) (hpos .fine)
      ha hab (fun ζ => finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) hm
      fun ζ => (finePairTimeFieldValue_abs ζ _).le

end FinePairRowRef

theorem response_absolute_cost_ge_one (q : ℕ) (hq : 1 ≤ q) :
    (1 : ℝ) ≤ ∑ j : Fin (2*q+2), |responseWeight q j| := by
  calc
    (1 : ℝ) = |∑ j : Fin (2*q+2), responseWeight q j * responseNode q j ^ 2| := by
      rw [response_second_moment q hq]; norm_num
    _ ≤ ∑ j : Fin (2*q+2), |responseWeight q j * responseNode q j ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin (2*q+2), |responseWeight q j| := Finset.sum_le_sum fun j _ => by
      rw [abs_mul, abs_of_nonneg (sq_nonneg (responseNode q j))]
      have hj := responseNode_mem_unit q j
      exact mul_le_of_le_one_right (abs_nonneg _) (by nlinarith [hj.1, hj.2, sq_nonneg (responseNode q j)])

theorem ordinary_density_absolute_cost_pos (a b : ℝ) (ha : 0 < a) (hab : a < b) (D : ℕ) :
    0 < ∑ h : HighDensityMarkIndex D 2 D, |densityPacketWeight a b D 2 D h| := by
  rw [densityPacketWeight_variation a b ha hab D 2 D (by norm_num)]
  have hp : densityPacketPrefactor a b 2 ≠ 0 := by
    change (2 : ℝ)^2 / (2 : ℝ) * (b / densityMargin a b 0)^2 ≠ 0
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (div_ne_zero (ha.trans hab).ne' (densityMargin_zero_ne a b ha hab)))
  have hn : 0 < (derivativeOrder D : ℝ) := by exact_mod_cast (show 0 < derivativeOrder D by unfold derivativeOrder; omega)
  exact mul_pos (mul_pos (abs_pos.mpr hp) (Real.cosh_pos _)) (pow_pos hn _)

theorem fine_density_absolute_cost_pos (a b : ℝ) (ha : 0 < a) (hab : a < b) (M : ℕ) :
    0 < ∑ h : FinePairDensityIndex M, |finePairDensityWeight a b M h| := by
  rw [finePairDensityWeight_variation a b ha hab M]
  exact mul_pos (mul_pos (by norm_num) (abs_pos.mpr
    (div_ne_zero (pow_ne_zero _ (ha.trans hab).ne') (pow_ne_zero _ (densityMargin_zero_ne a b ha hab)))))
    (Real.cosh_pos _)

theorem finePairRowMass_unit (d D M q : ℕ) (a b C T₀ N : ℝ) :
    finePairRowMass d D M q a b C T₀ N .unit =
      (∑ h : HighDensityMarkIndex D 2 D, |densityPacketWeight a b D 2 D h|) *
      (∑ h : Fin (2*q+2), |responseWeight q h|) * (2*C^2) *
      (∑ i, ∑ j, |finePairUnitMatrix d D i j|) := by
  rw [finePairRowMass, highPacketMarkMass_eq_variation (Measure.dirac ()) a b D 2 D q C
      (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _),
    highPacketSignedMeasure_totalVariation (Measure.dirac ()) a b D 2 D q C
      (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)]
  simp only [separatedMatrixCost, integral_dirac]

theorem finePairRowMass_coarse (d : ℕ) [NeZero d] (D M q : ℕ) (a b C T₀ N : ℝ) (hT : 0 ≤ T₀) :
    finePairRowMass d D M q a b C T₀ N .coarse =
      (∑ h : HighDensityMarkIndex D 2 D, |densityPacketWeight a b D 2 D h|) *
      (∑ h : Fin (2*q+2), |responseWeight q h|) * (2*C^2) *
      ((∑ i, ∑ j, |finePairDistanceMatrix d D i j|) * (T₀^2/2)) := by
  rw [finePairRowMass, highPacketMarkMass_eq_variation _ _ _ _ _ _ _ _ _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 T₀ _),
    highPacketSignedMeasure_totalVariation _ _ _ _ _ _ _ _ _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 T₀ _),
    finePairTimeMatrix_cost_integral d 0 T₀ le_rfl hT]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]

theorem finePairRowMass_fine (d : ℕ) [NeZero d] (D M q : ℕ) (a b C T₀ N : ℝ)
    (hT : 0 ≤ T₀) (hTN : T₀ ≤ N) :
    finePairRowMass d D M q a b C T₀ N .fine =
      (∑ h : FinePairDensityIndex M, |finePairDensityWeight a b M h|) *
      (∑ h : Fin (2*q+2), |responseWeight q h|) * (2*C^2) *
      ((∑ i, ∑ j, |finePairDistanceMatrix d D i j|) * ((N^2-T₀^2)/2)) := by
  rw [finePairRowMass, finePairPacketMarkMass,
    signedMarkMass_eq_variation _ _ (finePairPacketWeight_integrable _ a b M q C _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T₀ N _))]
  change ((finePairPacketSignedMeasure _ a b M q C _).variation univ).toReal = _
  rw [finePairPacketSignedMeasure_totalVariation _ a b M q C _
    (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T₀ N _),
    finePairTimeMatrix_cost_integral d T₀ N hT hTN]

def HigherBandCarrier (d r : ℕ) : Bool → Type
  | false => CardinalSeparatedMark d r
  | true => CardinalBandMark d r

instance higherBandCarrier_measurable (d r : ℕ) (fine : Bool) :
    MeasurableSpace (HigherBandCarrier d r fine) := by
  cases fine <;> dsimp [HigherBandCarrier] <;> infer_instance

instance higherBandCarrier_standardBorel (d r : ℕ) (fine : Bool) :
    StandardBorelSpace (HigherBandCarrier d r fine) := by
  cases fine
  · exact cardinal_separated_mark_standardBorel d r
  · exact cardinal_band_mark_standardBorel d r

def higherBandCarrierMeasure (d r : ℕ) (L T : ℝ) :
    (fine : Bool) → Measure (HigherBandCarrier d r fine)
  | false => cardinalSeparatedMeasure d r T
  | true => cardinalBandMeasure d r L T

def higherBandCarrierAmplitude (d r D : ℕ) (lam : ℝ) :
    (fine : Bool) → HigherBandCarrier d r fine → HighFrameIndex d D → HighFrameIndex d D → ℝ
  | false => cardinalSeparatedAmplitude lam
  | true => cardinalBandAmplitude lam

def higherBandCarrierFactor (d r : ℕ) (lam : ℝ) :
    (fine : Bool) → HigherBandCarrier d r fine → Fin r → Covariate d → ℝ
  | false => cardinalSeparatedFactor lam
  | true => cardinalBandFactor lam

theorem higherBandCarrierMeasure_finite (d r : ℕ) (L T : ℝ) (hT : 1 ≤ T) (fine : Bool) :
    IsFiniteMeasure (higherBandCarrierMeasure d r L T fine) := by
  cases fine
  · exact cardinal_separated_measure_finite d r hT
  · exact cardinal_band_measure_finite d r L hT

theorem higherBandCarrierAmplitude_measurable (d r D : ℕ) (lam : ℝ) (fine : Bool)
    (i j : HighFrameIndex d D) : Measurable fun ζ => higherBandCarrierAmplitude d r D lam fine ζ i j := by
  cases fine
  · exact cardinal_separated_amplitude_measurable lam i j
  · exact cardinal_band_amplitude_measurable lam i j

theorem higherBandCarrierAmplitude_cost_integrable (d r D : ℕ) (lam L T : ℝ) (hT : 1 ≤ T)
    (fine : Bool) : Integrable (separatedMatrixCost (higherBandCarrierAmplitude d r D lam fine))
      (higherBandCarrierMeasure d r L T fine) := by
  cases fine
  · exact cardinal_separated_cost_integrable lam hT
  · exact cardinal_band_cost_integrable lam L hT

theorem higherBandCarrierFactor_joint_measurable (d r : ℕ) (lam : ℝ) (fine : Bool) (l : Fin r) :
    Measurable fun ζx : HigherBandCarrier d r fine × Covariate d =>
      higherBandCarrierFactor d r lam fine ζx.1 l ζx.2 := by
  cases fine
  · exact cardinal_separated_factor_joint_measurable lam l
  · exact cardinal_band_factor_joint_measurable lam l

theorem higherBandCarrierFactor_bound (d r : ℕ) (lam : ℝ) (fine : Bool)
    (ζ : HigherBandCarrier d r fine) (l : Fin r) (x : Covariate d) (hx : ∀ i, |x i| ≤ 2) :
    |higherBandCarrierFactor d r lam fine ζ l x| ≤ 1 := by
  cases fine
  · exact cardinal_separated_factor_abs_le_one lam ζ l x hx
  · exact cardinal_band_factor_abs_le_one lam ζ l x hx

abbrev HigherBandRowMark (d r m D q : ℕ) (fine : Bool) :=
  HigherBandCarrier d r fine × HighPacketMarkIndex (HighFrameIndex d D) m r D q

def higherBandSignedRow (d r m D q : ℕ) (a b C lam L T : ℝ) (fine : Bool) :
    SignedMeasure (HigherBandRowMark d r m D q fine) :=
  highPacketSignedMeasure (higherBandCarrierMeasure d r L T fine) a b m r D q C
    (higherBandCarrierAmplitude d r D lam fine)

def higherBandRowMass (d r m D q : ℕ) (a b C lam L T : ℝ) (fine : Bool) : ℝ :=
  highPacketMarkMass (higherBandCarrierMeasure d r L T fine) a b m r D q C
    (higherBandCarrierAmplitude d r D lam fine)

def higherBandRowLaw (d r m D q : ℕ) (a b C lam L T : ℝ) (fine : Bool) :
    Measure (HigherBandRowMark d r m D q fine) :=
  highPacketAbsoluteLaw (higherBandCarrierMeasure d r L T fine) a b m r D q C
    (higherBandCarrierAmplitude d r D lam fine)

def higherBandRowActivation (d r m D q : ℕ) (a b C lam L T : ℝ) (fine : Bool) :
    HigherBandRowMark d r m D q fine → ℝ :=
  highPacketActivation (higherBandCarrierMeasure d r L T fine) a b m r D q C
    (higherBandCarrierAmplitude d r D lam fine)

def higherBandRowData (d k r m D q : ℕ) (a b C lam L T : ℝ) (fine : Bool) :
    HighUnionRowData d k D Unit fun _ => HigherBandRowMark d r m D q fine where
  rowLaw := fun _ => higherBandRowLaw d r m D q a b C lam L T fine
  rowMass := fun _ => higherBandRowMass d r m D q a b C lam L T fine
  rowActivation := fun _ => higherBandRowActivation d r m D q a b C lam L T fine
  rowIntercept := fun _ => highPacketIntercept a b m r D q
  rowSlope := fun j _ e x => highPacketSlope a b m r D q
    (fun ζ l => higherBandCarrierFactor d r lam fine ζ l (highLocalCoordinates d k j x)) e
  rowVector := fun _ e => (highResponseMarkAtom C q e.2.2).2
  rowTime := fun _ e => (highResponseMarkAtom 0 q e.2.2).1

theorem higherBandRowMass_eq_variation (d r m D q : ℕ) (a b C lam L T : ℝ)
    (hT : 1 ≤ T) (fine : Bool) : higherBandRowMass d r m D q a b C lam L T fine =
      ((higherBandSignedRow d r m D q a b C lam L T fine).variation univ).toReal := by
  letI := higherBandCarrierMeasure_finite d r L T hT fine
  exact highPacketMarkMass_eq_variation _ a b m r D q C _
    (higherBandCarrierAmplitude_measurable d r D lam fine)
    (higherBandCarrierAmplitude_cost_integrable d r D lam L T hT fine)

theorem higherBandRowMass_nonneg (d r m D q : ℕ) (a b C lam L T : ℝ) (fine : Bool) :
    0 ≤ higherBandRowMass d r m D q a b C lam L T fine := signedMarkMass_nonneg _ _

theorem higherBandRowActivation_bound (d r m D q : ℕ) (a b C lam L T : ℝ) (fine : Bool)
    (e : HigherBandRowMark d r m D q fine) :
    |higherBandRowActivation d r m D q a b C lam L T fine e| ≤ higherBandRowMass d r m D q a b C lam L T fine :=
  absoluteActivation_bound _ _ _

def higherBandInterpolationCap (d r : ℕ) (lam T : ℝ) : ℝ :=
  2 * (r : ℝ) * (1024 * |lam| * (d : ℝ)^2)^(r-1) * T^2 * (1+Real.log T)^(r-2)

def ordinaryDensityActivityBase (a b : ℝ) : ℝ :=
  Real.exp (1 + exteriorTau ((a+b)/(b-a))) * |b / densityMargin a b 0|

def higherBandRowActivityCap (d r m D q : ℕ) (a b C lam T : ℝ) : ℝ :=
  (ordinaryDensityActivityBase a b)^r * (D : ℝ)^r *
    Real.exp ((m : ℝ) * exteriorTau ((a+b)/(b-a))) *
    (∑ h : Fin (2*q+2), |responseWeight q h|) * (2*C^2) * higherBandInterpolationCap d r lam T

theorem higherBandRowMass_le_activityCap (d r m D q : ℕ) (hr : 2 ≤ r) (hD : 1 ≤ D)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (C lam L T : ℝ)
    (hT : 1 ≤ T) (hLT : L ≤ T) (fine : Bool) :
    higherBandRowMass d r m D q a b C lam L T fine ≤ higherBandRowActivityCap d r m D q a b C lam T := by
  letI := higherBandCarrierMeasure_finite d r L T hT fine
  rw [higherBandRowMass_eq_variation d r m D q a b C lam L T hT fine]
  refine (highPacketSignedMeasure_exponential_cost (higherBandCarrierMeasure d r L T fine)
    a b ha hab m r D q (by omega) hD C (higherBandCarrierAmplitude d r D lam fine)
    (higherBandCarrierAmplitude_measurable d r D lam fine)
    (higherBandCarrierAmplitude_cost_integrable d r D lam L T hT fine)).trans
    (mul_le_mul_of_nonneg_left ?_ (by positivity))
  cases fine
  · have h := cardinal_separated_cost_integral_le (d := d) (D := D) hr lam hT
    have hlog : 0 ≤ 1 + Real.log T := add_nonneg zero_le_one (Real.log_nonneg hT)
    have hb : 0 ≤ (r : ℝ) * (1024 * |lam| * (d : ℝ)^2)^(r-1) * T^2 * (1+Real.log T)^(r-2) := by positivity
    exact h.trans (by dsimp [higherBandInterpolationCap]; nlinarith)
  · exact cardinal_band_cost_integral_le hr lam L hT hLT

section HistoryStateAppend
variable {J : Type*} [Fintype J] [LinearOrder J]

def historyCanonicalWordMarks (dependent : J → J → Prop)
    (g : HistoryShape fun a b => ¬ dependent a b) {E : Type*}
    (marks : Fin (historyShapeLength dependent g) → E) : Fin g.out.length → E :=
  fun i => marks (Fin.cast (historyShapeLength_out dependent g).symm i)

def historyAppendWordMarks (dependent : J → J → Prop)
    (j : J) (g : HistoryShape fun a b => ¬ dependent a b)
    {E : Type*} [MeasurableSpace E] (fresh : E)
    (marks : Fin (historyShapeLength dependent g) → E) : Fin (g.out ++ [j]).length → E :=
  fun i => historyFiniteMarkAppendEquiv (historyShapeLength dependent g) (fresh, marks)
    (Fin.cast (by rw [historyShapeLength_out]; simp) i)

lemma historyMarkedRawState_append (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    {E X : Type*} [MeasurableSpace E] (update : J → E → X → X)
    (hcomm : ∀ j k, ¬ dependent j k → ∀ e f state,
      update k f (update j e state) = update j e (update k f state))
    (initial : X) (j : J) (h : HistoryMarked dependent E) (fresh : E) :
    historyMarkedRawState dependent update initial
      (historyMarkedAppend dependent hsymm j (h, fresh)) =
      update j fresh (historyMarkedRawState dependent update initial h) := by
  obtain ⟨g, marks⟩ := h
  have hword (g₀ : HistoryShape fun a b => ¬ dependent a b) (m₀ : Fin (historyShapeLength dependent g₀) → E) :
      historyMarkedRawState dependent update initial ⟨g₀, m₀⟩ =
        historyWordMarkedState update initial g₀.out (historyCanonicalWordMarks dependent g₀ m₀) := by
    have hm : (List.ofFn fun i : Fin (historyShapeLength dependent g₀) =>
        (historyShapeCanonicalLabels dependent g₀ i, m₀ i)) =
        (List.ofFn fun i : Fin (historyShapeLength dependent g₀) => i).map
          fun i => (historyShapeCanonicalLabels dependent g₀ i, m₀ i) := by rw [List.map_ofFn]; rfl
    have ht : (List.ofFn fun i : Fin (historyShapeLength dependent g₀) =>
        (historyShapeCanonicalLabels dependent g₀ i, m₀ i)) =
        List.ofFn fun i : Fin g₀.out.length => (g₀.out.get i, historyCanonicalWordMarks dependent g₀ m₀ i) := by
      refine List.ext_getElem (by simp only [List.length_ofFn]; exact historyShapeLength_out dependent g₀) fun i _ _ => ?_
      simp only [List.getElem_ofFn, historyShapeCanonicalLabels, historyCanonicalWordMarks]; congr 1
    have hh := congrArg (fun l : List (J × E) => l.foldl (fun state p => update p.1 p.2 state) initial) (hm.symm.trans ht)
    rwa [List.foldl_map] at hh
  have hcmark : historyCanonicalWordMarks dependent (historyShapeAppend dependent j g)
      (historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)) =
      historyHeapMarkEquiv (historyCanonicalAppendHeapIso dependent hsymm j g)
        (historyAppendWordMarks dependent j g fresh marks) := by
    let e := historyCanonicalAppendHeapIso dependent hsymm j g
    let hlen : historyShapeLength dependent g + 1 = (g.out ++ [j]).length := by rw [historyShapeLength_out]; simp
    ext i
    let x : WordHeapPiece (g.out ++ [j]) dependent := e.symm ⟨i⟩
    have hx : (e x).position = i := by simp only [x, e.apply_symm_apply]
    have hc : historyCanonicalAppendCoordinates dependent hsymm j g (Fin.cast hlen.symm x.position) =
        Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm (e x).position := by
      unfold historyCanonicalAppendCoordinates
      change Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm
        (historyHeapCoordinateEquiv e (Fin.cast hlen (Fin.cast hlen.symm x.position))) = _
      rw [Fin.cast_cast, Fin.cast_refl, historyHeapCoordinateEquiv_position]; rfl
    have hh := MeasurableEquiv.piCongrLeft_apply_apply
      (historyCanonicalAppendCoordinates dependent hsymm j g)
      (β := fun _ => E) (historyFiniteMarkAppendEquiv _ (fresh, marks)) (Fin.cast hlen.symm x.position)
    rw [hc, hx] at hh
    have ht := historyHeapMarkEquiv_position e (historyAppendWordMarks dependent j g fresh marks) x
    rw [hx] at ht
    exact hh.trans ht.symm
  have happ : historyWordMarkedState update initial (g.out ++ [j])
      (historyAppendWordMarks dependent j g fresh marks) =
      update j fresh (historyWordMarkedState update initial g.out
        (historyCanonicalWordMarks dependent g marks)) := by
    have ht : (List.ofFn fun i : Fin (g.out ++ [j]).length =>
        ((g.out ++ [j]).get i, historyAppendWordMarks dependent j g fresh marks i)) =
        (List.ofFn fun i : Fin g.out.length =>
          (g.out.get i, historyCanonicalWordMarks dependent g marks i)) ++ [(j, fresh)] := by
      refine List.ext_getElem (by simp only [List.length_ofFn, List.length_append, List.length_singleton]) fun i hi _ => ?_
      by_cases hiold : i < g.out.length
      · rw [List.getElem_append_left (by simpa only [List.length_ofFn] using hiold)]
        simp only [List.getElem_ofFn, List.get_eq_getElem, List.getElem_append_left hiold]
        refine congrArg (fun a => (g.out[i], a)) ?_
        unfold historyAppendWordMarks historyCanonicalWordMarks
        rw [show Fin.cast (by rw [historyShapeLength_out]; simp) (⟨i, by simpa only [List.length_ofFn] using hi⟩ : Fin (g.out ++ [j]).length) =
          (Fin.cast (historyShapeLength_out dependent g).symm ⟨i, hiold⟩).castSucc from Fin.ext rfl,
          historyFiniteMarkAppendEquiv_old]
      · have hieq : i = g.out.length := by
          simp only [List.length_ofFn, List.length_append, List.length_singleton] at hi; omega
        subst i
        rw [List.getElem_append_right (by simp only [List.length_ofFn]; exact le_rfl)]
        simp only [List.length_ofFn, Nat.sub_self, List.getElem_cons_zero, List.getElem_ofFn,
          List.get_eq_getElem, List.getElem_append_right le_rfl]
        refine congrArg (fun a => (j, a)) ?_
        unfold historyAppendWordMarks
        rw [show Fin.cast (by rw [historyShapeLength_out]; simp) (⟨g.out.length, by simpa only [List.length_ofFn] using hi⟩ : Fin (g.out ++ [j]).length) =
          Fin.last (historyShapeLength dependent g) from Fin.ext (historyShapeLength_out dependent g).symm,
          historyFiniteMarkAppendEquiv_last]
    unfold historyWordMarkedState historyWordState
    rw [ht, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change historyMarkedRawState dependent update initial
    ⟨historyShapeAppend dependent j g, historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)⟩ = _
  rw [hword, hcmark, historyHeapMarkEquiv_state dependent hsymm update hcomm
    (historyCanonicalAppendHeapIso dependent hsymm j g)
    (historyCanonicalAppendHeapIso_label dependent hsymm j g), happ, ← hword]

end HistoryStateAppend

section UnionHistory
attribute [local instance] Classical.propDecidable

section FiniteHistory
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] (R : HighUnionRowData d k F I E)

def highUnionHistoryState (δ : ℝ) (n : ℕ) (labels : Fin n → HighWindowLabels d k)
    (initial : HighRawState d k F) (marks : Fin n → HighUnionMark E) : HighRawState d k F :=
  (List.ofFn fun i : Fin n => i).foldl
    (fun θ i => highUnionRawUpdate R δ (labels i) (marks i) θ) initial

theorem highUnionHistory_density_joint_measurable [∀ i, StandardBorelSpace (E i)]
    (hSlope : ∀ j i, Measurable fun ex : E i × Covariate d => R.rowSlope j i ex.1 ex.2)
    (hOffset : ∀ i, Measurable (R.rowIntercept i)) (δ : ℝ)
    (n : ℕ) (labels : Fin n → HighWindowLabels d k)
    (initial : HighRawState d k F) (hi : Measurable initial.1) :
    Measurable fun mx : (Fin n → HighUnionMark E) × Covariate d =>
      (highUnionHistoryState R δ n labels initial mx.1).1 mx.2 :=
  affinePatchFold_density_joint_measurable (highTorusPatch d k)
    (highTorusPatch_measurableSet d k) (highUnionSlope R)
    (fun _ e _ => highUnionIntercept R δ e)
    (fun j => highUnionSlope_joint_measurable R hSlope j)
    (fun _ => (highUnionIntercept_measurable R hOffset δ).comp measurable_fst)
    (fun _ => highUnionResponseReset R) n labels (List.ofFn fun i : Fin n => i)
    (fun _ => initial) (hi.comp measurable_snd)

theorem highUnionHistory_density_mean_one [∀ i, IsProbabilityMeasure (R.rowLaw i)]
    (hMass : ∀ i, 0 ≤ R.rowMass i) (hTotal : 0 < highRowTotalMass R.rowMass)
    (hSlope : ∀ j x i, Measurable fun e => R.rowSlope j i e x)
    (hiSlope : ∀ j x i, Integrable (fun e => R.rowSlope j i e x) (R.rowLaw i))
    (hcSlope : ∀ j x i, (∫ e, R.rowSlope j i e x ∂(R.rowLaw i)) = 0)
    (hOffset : ∀ i, Measurable (R.rowIntercept i))
    (a b : ℝ) (hOffsetBound : ∀ i e, R.rowIntercept i e ∈ Icc a b)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (n : ℕ) (labels : Fin n → HighWindowLabels d k)
    (initial : HighRawState d k F) (hinit : ∀ x, initial.1 x = 1) (x : Covariate d) :
    (∫ marks, (highUnionHistoryState R δ n labels initial marks).1 x
      ∂Measure.pi fun _ : Fin n => highUnionLaw R δ) = 1 := by
  let π := highUnionLaw R δ
  letI : IsProbabilityMeasure π := highUnionLaw_probability R hMass hTotal δ hδ0 hδ1.le
  let s := fun (j : HighWindowLabels d k) (e : HighUnionMark E) =>
    if x ∈ highTorusPatch d k j then highUnionSlope R j e x else 1
  let o := fun (j : HighWindowLabels d k) (e : HighUnionMark E) =>
    if x ∈ highTorusPatch d k j then highUnionIntercept R δ e else 0
  have hs (j) : Integrable (s j) π := by
    by_cases hx : x ∈ highTorusPatch d k j
    · simp only [s, if_pos hx]
      exact balancedReferenceLaw_integrable _ δ _
        (highCenteredRowUnionSlope_measurable _ (hSlope j x))
        (highRowReferenceUnion_integrable R.rowLaw R.rowMass _
          (rowSigmaFunction_measurable _ (hSlope j x)) (hiSlope j x))
    · simp only [s, if_neg hx]; exact integrable_const _
  have ho (j) : Integrable (o j) π := by
    by_cases hx : x ∈ highTorusPatch d k j
    · simp only [o, if_pos hx]
      exact balancedReferenceLaw_integrable _ δ _ (highUnionIntercept_measurable R hOffset δ)
        (highRowReferenceUnion_integrable R.rowLaw R.rowMass _
          (rowSigmaFunction_measurable _ hOffset) fun i =>
            boundedIntercept_integrable (R.rowLaw i) (R.rowIntercept i) (hOffset i) a b (hOffsetBound i))
    · simp only [o, if_neg hx]; exact integrable_const _
  have hmean (j) : (∫ e, s j e ∂π) + (∫ e, o j e ∂π) = 1 := by
    by_cases hx : x ∈ highTorusPatch d k j
    · simp only [s, o, if_pos hx]
      change (∫ e, highCenteredRowUnionSlope (fun i e => R.rowSlope j i e x) e
        ∂highCenteredRowUnionLaw R.rowLaw R.rowMass δ) +
        (∫ e, highCenteredRowUnionIntercept R.rowLaw R.rowMass R.rowIntercept δ e
          ∂highCenteredRowUnionLaw R.rowLaw R.rowMass δ) = 1
      rw [highCenteredRowUnionSlope_integral_zero R.rowLaw R.rowMass hMass hTotal
          _ (hSlope j x) (hiSlope j x) (hcSlope j x) δ hδ0 hδ1.le,
        highCenteredRowUnionIntercept_integral_one R.rowLaw R.rowMass hMass hTotal
          R.rowIntercept hOffset a b hOffsetBound δ hδ0 hδ1]
      norm_num
    · simp [s, o, hx]
  convert finiteAffineHistory_integral_one π s o hs ho hmean n labels using 1
  exact integral_congr_ae <| Filter.Eventually.of_forall fun marks =>
    (affinePatchFold_density_eq (highTorusPatch d k) (highUnionSlope R)
      (fun _ e _ => highUnionIntercept R δ e) (fun _ => highUnionResponseReset R)
      labels marks (List.ofFn fun i : Fin n => i) initial x).trans (by rw [hinit x]; rfl)

theorem highUnionHistory_density_interval (δ a b : ℝ)
    (hLegal : ∀ j e x v, v ∈ Icc a b →
      highUnionSlope R j e x * v + highUnionIntercept R δ e ∈ Icc a b)
    (n : ℕ) (labels : Fin n → HighWindowLabels d k) (initial : HighRawState d k F)
    (hi : ∀ x, initial.1 x ∈ Icc a b) (marks : Fin n → HighUnionMark E) (x : Covariate d) :
    (highUnionHistoryState R δ n labels initial marks).1 x ∈ Icc a b :=
  affineRawHistory_density_interval (highTorusPatch d k) (highUnionSlope R)
    (fun _ e _ => highUnionIntercept R δ e) (fun _ => highUnionResponseReset R)
    labels (List.ofFn fun i : Fin n => i) marks a b hLegal initial hi x

theorem highUnionHistory_coefficient_ball (δ Cfr : ℝ) (hCfr : 0 < Cfr)
    (hVector : ∀ i e, (∑ γ, |R.rowVector i e γ|) ≤ Cfr⁻¹)
    (hTime : ∀ i e, R.rowTime i e ∈ Icc (0 : ℝ) 1)
    (n : ℕ) (labels : Fin n → HighWindowLabels d k) (initial : HighRawState d k F)
    (hi : ∀ j, (∑ γ, |initial.2 j γ|) ≤ Cfr⁻¹) (marks : Fin n → HighUnionMark E) :
    ∀ j, (∑ γ, |(highUnionHistoryState R δ n labels initial marks).2 j γ|) ≤ Cfr⁻¹ := by
  suffices hf : ∀ indices : List (Fin n), ∀ init : HighRawState d k F,
      (∀ j, (∑ γ, |init.2 j γ|) ≤ Cfr⁻¹) → ∀ j,
      (∑ γ, |(indices.foldl (fun θ i => highUnionRawUpdate R δ (labels i) (marks i) θ) init).2 j γ|) ≤ Cfr⁻¹ from
    hf _ initial hi
  intro indices; induction indices with
  | nil => intro init hi j; exact hi j
  | cons i indices ih =>
    intro init hi; refine ih _ fun j => ?_
    by_cases hj : j = labels i
    · subst j
      change (∑ γ, |(Function.update init.2 (labels i)
        (highUnionResponseReset R (marks i) (init.2 (labels i)))) (labels i) γ|) ≤ _
      rw [Function.update_self]
      exact highUnionResponseReset_ball R Cfr hCfr hVector hTime _ _ (hi _)
    · simpa only [highUnionRawUpdate, rawPatchUpdate, responseCoordinateUpdate,
        Function.update_of_ne hj] using hi j

end FiniteHistory

section CanonicalHistory
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (R : HighUnionRowData d k F I E)
  (dependent : HighWindowLabels d k → HighWindowLabels d k → Prop)

def highUnionMarkedState (δ : ℝ) (initial : HighRawState d k F)
    (h : HistoryMarked dependent (HighUnionMark E)) : HighRawState d k F :=
  historyMarkedRawState dependent (highUnionRawUpdate R δ) initial h

def highUnionMarkedDensity (δ : ℝ) (initial : HighRawState d k F)
    (h : HistoryMarked dependent (HighUnionMark E)) (x : Covariate d) : ℝ :=
  (highUnionMarkedState R dependent δ initial h).1 x

def highUnionMarkedMass (δ : ℝ) (initial : HighRawState d k F)
    (h : HistoryMarked dependent (HighUnionMark E)) : ℝ :=
  ∫ x, highUnionMarkedDensity R dependent δ initial h x ∂cubeVolume d

theorem highUnionMarkedDensity_joint_measurable [∀ i, StandardBorelSpace (E i)]
    (hSlope : ∀ j i, Measurable fun ex : E i × Covariate d => R.rowSlope j i ex.1 ex.2)
    (hOffset : ∀ i, Measurable (R.rowIntercept i)) (δ : ℝ)
    (initial : HighRawState d k F) (hi : Measurable initial.1) :
    Measurable fun hx : HistoryMarked dependent (HighUnionMark E) × Covariate d =>
      highUnionMarkedDensity R dependent δ initial hx.1 hx.2 := by
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  let X := fun g : HistoryShape fun i j => ¬ dependent i j =>
    Fin (historyShapeLength dependent g) → HighUnionMark E
  let G : Sigma (fun g => X g × Covariate d) → ℝ := fun hx =>
    highUnionMarkedDensity R dependent δ initial ⟨hx.1, hx.2.1⟩ hx.2.2
  exact ((historySigma_measurable_iff G).mpr fun g =>
    highUnionHistory_density_joint_measurable R hSlope hOffset δ
      (historyShapeLength dependent g) (historyShapeCanonicalLabels dependent g) initial hi).comp
    (historySigmaProdMeasurableEquiv X (Covariate d)).measurable

theorem highUnionMarkedMass_measurable [∀ i, StandardBorelSpace (E i)]
    (hSlope : ∀ j i, Measurable fun ex : E i × Covariate d => R.rowSlope j i ex.1 ex.2)
    (hOffset : ∀ i, Measurable (R.rowIntercept i)) (δ : ℝ)
    (initial : HighRawState d k F) (hi : Measurable initial.1) :
    Measurable (highUnionMarkedMass R dependent δ initial) := by
  letI := cubeVolume_isProbability d
  exact (highUnionMarkedDensity_joint_measurable R dependent hSlope hOffset δ initial hi).stronglyMeasurable.integral_prod_right'.measurable

theorem highUnionMarkedState_append (δ : ℝ) (initial : HighRawState d k F)
    (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (fresh : HighUnionMark E) :
    highUnionMarkedState R (fun i j => j ∈ highNeighborLabels d k i) δ initial
      (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h, fresh)) =
      highUnionRawUpdate R δ j fresh
        (highUnionMarkedState R (fun i j => j ∈ highNeighborLabels d k i) δ initial h) :=
  historyMarkedRawState_append (fun i j => j ∈ highNeighborLabels d k i)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) (highUnionRawUpdate R δ)
    (fun i l hne e f state => rawPatchUpdate_commute _ _ _ _ _ _ _ _
      (fun he => by subst he; exact hne (highNeighborLabels_self_mem d k i))
      (highTorusPatch_disjoint_of_not_neighbor d k i l hne) state)
    initial j h fresh

end CanonicalHistory
end UnionHistory
end UnionRowsAndHistory

-- ============================================================================
-- 4. Invariant Observable, Concentration, Mass-Tilt Tail, and Append Likelihood
-- ============================================================================

section ConcentrationAndTiltedLikelihood

section HistoryConcentration
variable {J : Type*} [Fintype J] [LinearOrder J]

theorem historyMarkedPrior_invariant_observable (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T B : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B)
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F : HistoryMarked dependent E → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M)
    (hkill : ∀ j h, ∫ e, F (historyMarkedAppend dependent hsymm j (h, e)) * a e ∂π = 0)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (∫ h, F h ∂historyMarkedPrior dependent Δ t π a) = ∫ h, F h ∂historyMarkedReference dependent Δ π := by
  let μ := historyMarkedReference dependent Δ π
  let : IsProbabilityMeasure μ := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
  let f := historyMarkedExpectation dependent (historyReferenceRho Δ) μ a F
  have hs (u : ℝ) (hu : u ∈ Icc 0 T) : u * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hB) (historyReferenceRho_pos Δ).le).trans hsmall
  have hAC : AbsolutelyContinuousOnInterval f 0 T :=
    historyMarkedExpectation_absolutelyContinuous dependent hrefl hsymm Δ hlabels
      (historyReferenceRho Δ) T B (historyReferenceRho_pos Δ) hT hB μ a ha habound hsmall F hF M hM hFbound
  have hn0 : ∀ᵐ u : ℝ, u ≠ 0 := by rw [ae_iff]; simp
  have hnT : ∀ᵐ u : ℝ, u ≠ T := by rw [ae_iff]; simp
  have hzero : ∀ᵐ u : ℝ, u ∈ uIcc 0 T → HasDerivAt f 0 u := by
    filter_upwards [hn0, hnT] with u hu0 huT hu
    rw [uIcc_of_le hT] at hu
    have hd := historyMarkedExpectation_weak_transport dependent hrefl hsymm Δ hΔ hlabels
      T B u (lt_of_le_of_ne hu.1 (Ne.symm hu0)) (lt_of_le_of_ne hu.2 huT) hB
      π a ha habound hsmall F hF M hM hFbound
    have hgen0 : historyMarkedGeneratorExpectation dependent hsymm (historyReferenceRho Δ) u μ π a F = 0 := by
      unfold historyMarkedGeneratorExpectation
      refine Finset.sum_eq_zero fun j _ => ?_
      let G := fun p : HistoryMarked dependent E × E =>
        F (historyMarkedAppend dependent hsymm j p) * a p.2 *
          historyMarkedDensity dependent (historyReferenceRho Δ) u a p.1
      have hG : Measurable G :=
        ((hF.comp (historyMarkedAppend_measurable dependent hsymm j)).mul (ha.comp measurable_snd)).mul
          ((historyMarkedDensity_measurable dependent _ u a ha).comp measurable_fst)
      have hInt : Integrable G (μ.prod π) :=
        Integrable.of_bound hG.aestronglyMeasurable (M * B * (3 / 2 : ℝ) ^ Fintype.card J) <|
          Eventually.of_forall fun p => by
            change ‖F (historyMarkedAppend dependent hsymm j p) * a p.2 *
              historyMarkedDensity dependent (historyReferenceRho Δ) u a p.1‖ ≤ _
            rw [Real.norm_eq_abs, abs_mul, abs_mul]
            have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels
              (historyReferenceRho Δ) u B (historyReferenceRho_pos Δ) hu.1 hB a habound (hs u hu) p.1
            have hp : 0 ≤ historyMarkedDensity dependent (historyReferenceRho Δ) u a p.1 :=
              (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
            rw [abs_of_nonneg hp]
            exact mul_le_mul (mul_le_mul (hFbound _) (habound _) (abs_nonneg _) hM) hb.2 hp (mul_nonneg hM hB)
      change (∫ p, G p ∂μ.prod π) = 0
      rw [integral_prod G hInt]
      simp_rw [show ∀ h, ∫ e, G (h, e) ∂π = 0 from fun h => by
        dsimp only [G]; rw [integral_mul_const, hkill j h, zero_mul]]
      exact integral_zero _ _
    rwa [hgen0] at hd
  obtain ⟨C, hC⟩ := hAC.const_of_ae_hasDerivAt_zero hzero
  have hft : f t = f 0 := (hC t (by simpa only [uIcc_of_le hT] using ht)).trans
    (hC 0 (by simp only [uIcc_of_le hT, mem_Icc]; exact ⟨le_rfl, hT⟩)).symm
  rw [historyMarkedPrior_integral_eq_expectation dependent hrefl hsymm Δ hlabels
    t B ht.1 hB π a ha habound (hs t ht) F]
  change f t = _; rw [hft]
  simp [f, μ, historyMarkedExpectation, historyMarkedDensity_zero]

lemma historyMarkedReference_integral_le_of_fiber_bound (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π]
    (F : HistoryMarked dependent E → ℝ) (hF : Measurable F)
    (R C : ℝ) (hbound : ∀ h, |F h| ≤ R)
    (hconditional : ∀ g, (∫ marks, F ⟨g, marks⟩
      ∂Measure.pi fun _ : Fin (historyShapeLength dependent g) => π) ≤ C) :
    (∫ h, F h ∂historyMarkedReference dependent Δ π) ≤ C := by
  let μ := historyMarkedReferenceRaw dependent Δ π
  let : IsFiniteMeasure μ := historyMarkedReferenceRaw_finite dependent hrefl hsymm Δ hΔ hlabels π
  let : IsProbabilityMeasure (historyMarkedReference dependent Δ π) :=
    historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
  have hi : Integrable F μ := Integrable.of_bound hF.aestronglyMeasurable R
    (Eventually.of_forall fun h => by simpa only [Real.norm_eq_abs] using hbound h)
  have hc : Integrable (fun _ : HistoryMarked dependent E => C) μ := integrable_const C
  have hr : (∫ h, F h ∂μ) ≤ ∫ _ : HistoryMarked dependent E, C ∂μ := by
    change (∫ h, F h ∂Measure.sum _) ≤ ∫ _ : HistoryMarked dependent E, C ∂Measure.sum _
    rw [integral_sum_measure hi, integral_sum_measure hc]
    refine Summable.tsum_le_tsum (fun g => ?_)
      (hasSum_integral_measure hi).summable (hasSum_integral_measure hc).summable
    rw [integral_smul_measure, integral_smul_measure,
      integral_map (historyMarked_measurable_mk dependent g).aemeasurable hF.aestronglyMeasurable,
      integral_map (historyMarked_measurable_mk dependent g).aemeasurable measurable_const.aestronglyMeasurable]
    simpa [smul_eq_mul] using mul_le_mul_of_nonneg_left (hconditional g) ENNReal.toReal_nonneg
  have he : (∫ h, F h ∂historyMarkedReference dependent Δ π) ≤
      ∫ _ : HistoryMarked dependent E, C ∂historyMarkedReference dependent Δ π := by
    unfold historyMarkedReference
    rw [integral_smul_measure, integral_smul_measure]
    exact mul_le_mul_of_nonneg_left hr ENNReal.toReal_nonneg
  simpa using he

theorem historyMarkedReference_mean_one (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π]
    (m : HistoryMarked dependent E → ℝ) (hm : Measurable m) (R : ℝ) (hbound : ∀ h, |m h| ≤ R)
    (hmean : ∀ g, (∫ marks, m ⟨g, marks⟩
      ∂Measure.pi fun _ : Fin (historyShapeLength dependent g) => π) = 1) :
    (∫ h, m h ∂historyMarkedReference dependent Δ π) = 1 := by
  have hu := historyMarkedReference_integral_le_of_fiber_bound dependent hrefl hsymm Δ hΔ hlabels
    π m hm R 1 hbound fun g => (hmean g).le
  have hl := historyMarkedReference_integral_le_of_fiber_bound dependent hrefl hsymm Δ hΔ hlabels
    π (fun h => -m h) hm.neg R (-1) (fun h => by simpa only [abs_neg] using hbound h)
    fun g => by rw [integral_neg, hmean g]
  rw [integral_neg] at hl; linarith

lemma label_block_centered_mgf_le {I E : Type*} [Fintype I] [MeasurableSpace E] [Nonempty E]
    (labels : I → J) (π : Measure E) [IsProbabilityMeasure π]
    (F : (I → E) → ℝ) (hF : Measurable F) (R c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ marks, |F marks| ≤ R)
    (hosc : ∀ j marks marks', (∀ i, labels i ≠ j → marks i = marks' i) → |F marks - F marks'| ≤ c)
    (u : ℝ) :
    (∫ marks, Real.exp (u * (F marks - ∫ marks', F marks' ∂Measure.pi fun _ : I => π))
      ∂Measure.pi fun _ : I => π) ≤ Real.exp ((Fintype.card J : ℝ) * u ^ 2 * c ^ 2 / 8) := by
  classical
  let recn (blocks : J → I → E) : I → E := fun i => blocks (labels i) i
  have hrecM : Measurable recn := measurable_pi_iff.2 fun i => (measurable_pi_apply i).comp (measurable_pi_apply (labels i))
  let ν := Measure.pi fun _ : I => π
  let μ := Measure.pi fun _ : J => ν
  have hp : MeasurePreserving recn μ ν := by
    refine ⟨hrecM, (Measure.pi_eq (μ := fun _ : I => π) fun s hs => ?_).symm⟩
    rw [Measure.map_apply hrecM (MeasurableSet.univ_pi hs),
      show recn ⁻¹' Set.univ.pi s = Set.univ.pi fun j : J => Set.univ.pi fun i : I => if labels i = j then s i else Set.univ by
        ext blocks
        simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, recn]
        exact ⟨fun h j i => by
            by_cases hij : labels i = j
            · simpa only [hij, ite_true] using h i
            · simp only [hij, ite_false, Set.mem_univ],
          fun h i => by simpa only [ite_true] using h (labels i) i⟩,
      Measure.pi_pi]
    dsimp only [ν]
    simp_rw [Measure.pi_pi, show ∀ j i, π (if labels i = j then s i else Set.univ) =
      if labels i = j then π (s i) else 1 from fun j i => by
        by_cases h : labels i = j
        · simp only [h, ite_true]
        · simp only [h, ite_false, measure_univ]]
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun _ _ => by simp
  let G := F ∘ recn
  have hG : Measurable G := hF.comp hrecM
  let f := (Fintype.equivFin J).symm
  let eqv := MeasurableEquiv.piCongrLeft (fun _ : J => I → E) f
  have hpE : MeasurePreserving eqv (Measure.pi fun _ : Fin (Fintype.card J) => ν) μ :=
    measurePreserving_piCongrLeft (fun _ : J => ν) f
  have hGo (k : Fin (Fintype.card J)) (x : Fin (Fintype.card J) → I → E) (y : I → E) :
      |(G ∘ eqv) (Function.update x k y) - (G ∘ eqv) x| ≤ c := by
    have he : eqv (Function.update x k y) = Function.update (eqv x) (f k) y := by
      funext j; obtain ⟨l, rfl⟩ := f.surjective j
      change MeasurableEquiv.piCongrLeft (fun _ : J => I → E) f (Function.update x k y) (f l) = _
      rw [MeasurableEquiv.piCongrLeft_apply_apply]
      by_cases hl : l = k
      · subst l; simp
      · rw [Function.update_of_ne hl, Function.update_of_ne fun h => hl (f.injective h)]
        exact (MeasurableEquiv.piCongrLeft_apply_apply f (β := fun _ : J => I → E) x l).symm
    dsimp only [Function.comp_apply]; rw [he]
    exact hosc (f k) _ _ fun i hi => by dsimp only [recn]; rw [Function.update_of_ne hi]
  have hh := product_centered_mgf_le (Fintype.card J) (fun _ => ν) (G ∘ eqv)
    (hG.comp eqv.measurable) R c hc (fun x => hbound (recn (eqv x))) hGo u
  have hmE : (∫ x, (G ∘ eqv) x ∂Measure.pi fun _ => ν) = ∫ blocks, G blocks ∂μ := hpE.integral_comp' G
  rw [hmE] at hh
  change (∫ x, Real.exp (u * (G (eqv x) - ∫ blocks, G blocks ∂μ)) ∂Measure.pi fun _ => ν) ≤ _ at hh
  rw [hpE.integral_comp' fun blocks => Real.exp (u * (G blocks - ∫ b, G b ∂μ))] at hh
  have hm : (∫ blocks, G blocks ∂μ) = ∫ marks, F marks ∂ν :=
    (integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable).symm.trans
      (congrArg (fun m => ∫ marks, F marks ∂m) hp.map_eq)
  change (∫ blocks, Real.exp (u * (G blocks - ∫ blocks', G blocks' ∂μ)) ∂μ) ≤ _ at hh
  rw [hm] at hh
  have hmeas : Measurable fun marks => Real.exp (u * (F marks - ∫ marks', F marks' ∂ν)) :=
    Real.measurable_exp.comp (measurable_const.mul (hF.sub measurable_const))
  have hi : (∫ blocks, Real.exp (u * (G blocks - ∫ marks, F marks ∂ν)) ∂μ) =
      ∫ marks, Real.exp (u * (F marks - ∫ marks', F marks' ∂ν)) ∂ν :=
    (integral_map hp.measurable.aemeasurable hmeas.aestronglyMeasurable).symm.trans
      (congrArg (fun m => ∫ marks, Real.exp (u * (F marks - ∫ marks', F marks' ∂ν)) ∂m) hp.map_eq)
  rwa [hi] at hh

theorem historyMarkedReference_mass_mgf (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    {E : Type*} [MeasurableSpace E] [Nonempty E] (π : Measure E) [IsProbabilityMeasure π]
    (m : HistoryMarked dependent E → ℝ) (hm : Measurable m)
    (R c : ℝ) (hc : 0 ≤ c) (hbound : ∀ h, |m h| ≤ R)
    (hmean : ∀ g, (∫ marks, m ⟨g, marks⟩
      ∂Measure.pi fun _ : Fin (historyShapeLength dependent g) => π) = 1)
    (hosc : ∀ g j (marks marks' : Fin (historyShapeLength dependent g) → E),
      (∀ i, historyShapeCanonicalLabels dependent g i ≠ j → marks i = marks' i) →
        |m ⟨g, marks⟩ - m ⟨g, marks'⟩| ≤ c) (u : ℝ) :
    (∫ h, Real.exp (u * (m h - 1)) ∂historyMarkedReference dependent Δ π) ≤
      Real.exp ((Fintype.card J : ℝ) * u ^ 2 * c ^ 2 / 8) := by
  let F := fun h : HistoryMarked dependent E => Real.exp (u * (m h - 1))
  have hF : Measurable F := Real.measurable_exp.comp (measurable_const.mul (hm.sub measurable_const))
  have hFb (h) : |F h| ≤ Real.exp (|u| * (R + 1)) := by
    rw [abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
    rw [abs_mul]
    have hh := abs_sub (m h) 1; norm_num only [abs_one] at hh
    exact mul_le_mul_of_nonneg_left (by linarith [hbound h]) (abs_nonneg _)
  refine historyMarkedReference_integral_le_of_fiber_bound dependent hrefl hsymm Δ hΔ hlabels π F hF
    (Real.exp (|u| * (R + 1))) _ hFb fun g => ?_
  have hh := label_block_centered_mgf_le (historyShapeCanonicalLabels dependent g) π
    (fun marks => m ⟨g, marks⟩) (hm.comp (historyMarked_measurable_mk dependent g))
    R c hc (fun marks => hbound ⟨g, marks⟩) (hosc g) u
  rwa [hmean g] at hh

end HistoryConcentration

theorem massPowerTilt_abs_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (l b : ℝ) (hl : 0 < l)
    (hbound : ∀ ω, l ≤ m ω ∧ m ω ≤ b) (hmean : ∫ ω, m ω ∂μ = 1)
    (a ε : ℝ) (ha : 0 < a)
    (hmgf : ∀ u : ℝ, (∫ ω, Real.exp (u * (m ω - 1)) ∂μ) ≤ Real.exp (a * u ^ 2))
    (hε : 8 * a * (n : ℝ) ≤ ε) :
    (massPowerTilt μ m n).real {ω | ε < |m ω - 1|} ≤ 2 * Real.exp (-ε ^ 2 / (8 * a)) := by
  let _ := massPowerTilt_isProbability μ m hm n l b hl hbound
  have hGpos := massPowerNormalizer_pos μ m hm n l b hl hbound
  have him : Integrable m μ := by simpa only [pow_one] using massPower_integrable μ m hm 1 l b hl hbound
  have hI := massPower_integrable μ m hm n l b hl hbound
  have hG : 1 ≤ massPowerNormalizer μ m n := by
    have hsubI : Integrable (fun ω => m ω - 1) μ := him.sub (integrable_const 1)
    have hh : (∫ ω, 1 + (n : ℝ) * (m ω - 1) ∂μ) ≤ ∫ ω, m ω ^ n ∂μ :=
      integral_mono ((integrable_const 1).add (hsubI.const_mul (n : ℝ))) hI
        fun ω => one_add_mul_sub_le_pow ((by norm_num : (-1 : ℝ) ≤ 0).trans (hl.le.trans (hbound ω).1)) n
    have he : (∫ ω, 1 + (n : ℝ) * (m ω - 1) ∂μ) = 1 :=
      (integral_add (integrable_const 1) (hsubI.const_mul (n : ℝ))).trans
        (by rw [integral_const_mul, integral_sub him (integrable_const 1), hmean]; simp)
    rwa [he] at hh
  have hreal (S : Set Ω) (hS : MeasurableSet S) :
      (massPowerTilt μ m n).real S = ∫ ω, S.indicator (fun ω => m ω ^ n / massPowerNormalizer μ m n) ω ∂μ := by
    rw [← integral_indicator_one hS, massPowerTilt,
      integral_withDensity_eq_integral_toReal_smul ((hm.pow_const n).div_const _).ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae <| Eventually.of_forall fun ω => ?_
    have hp : 0 ≤ m ω ^ n / massPowerNormalizer μ m n :=
      div_nonneg (pow_nonneg (hl.le.trans (hbound ω).1) _) hGpos.le
    by_cases hω : ω ∈ S <;> simp [hω, ENNReal.toReal_ofReal hp, smul_eq_mul]
  have hexpI (u : ℝ) : Integrable (fun ω => Real.exp (u * (m ω - 1))) μ :=
    Integrable.of_bound (Real.measurable_exp.comp (measurable_const.mul (hm.sub measurable_const))).aestronglyMeasurable
      (Real.exp (|u| * (|b| + 1))) <| Eventually.of_forall fun ω => by
        change ‖Real.exp (u * (m ω - 1))‖ ≤ _
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
        rw [abs_mul]
        have hmabs : |m ω| ≤ |b| := by rw [abs_of_pos (hl.trans_le (hbound ω).1)]; exact (hbound ω).2.trans (le_abs_self b)
        have hh := abs_sub (m ω) 1; norm_num only [abs_one] at hh
        exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg u)
  have he0 : 0 ≤ ε := (by positivity : (0 : ℝ) ≤ 8 * a * (n : ℝ)).trans hε
  let uR := ε / (2 * a) - (n : ℝ)
  have huR : 0 ≤ uR := sub_nonneg.2 ((le_div_iff₀ (by positivity : (0 : ℝ) < 2 * a)).2 (by nlinarith [Nat.cast_nonneg (α := ℝ) n]))
  have hr : (massPowerTilt μ m n).real {ω | ε < m ω - 1} ≤ Real.exp (-ε ^ 2 / (8 * a)) := by
    let SR := {ω | ε < m ω - 1}
    have hSR : MeasurableSet SR := measurableSet_lt measurable_const (hm.sub measurable_const)
    have hch : (massPowerTilt μ m n).real SR ≤ Real.exp (-uR * ε) * ∫ ω, Real.exp (((n : ℝ) + uR) * (m ω - 1)) ∂μ := by
      rw [hreal SR hSR, ← integral_const_mul]
      refine integral_mono ((hI.div_const _).indicator hSR) ((hexpI ((n : ℝ) + uR)).const_mul _) fun ω => ?_
      by_cases hω : ω ∈ SR
      · simp only [Set.indicator_of_mem hω]
        have hm0 : 0 ≤ m ω := hl.le.trans (hbound ω).1
        have hbase : m ω ≤ Real.exp (m ω - 1) := by linarith [Real.add_one_le_exp (m ω - 1)]
        refine (div_le_self (pow_nonneg hm0 n) hG).trans ((pow_le_pow_left₀ hm0 hbase n).trans ?_)
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        have hh : ε ≤ m ω - 1 := hω.le
        exact Real.exp_le_exp.2 (by nlinarith [mul_nonneg huR (sub_nonneg.2 hh)])
      · simp only [Set.indicator_of_notMem hω]; positivity
    have he : (n : ℝ) * ε ≤ ε ^ 2 / (8 * a) :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * a)).2 (by nlinarith [mul_nonneg he0 (sub_nonneg.2 hε)])
    refine (hch.trans (mul_le_mul_of_nonneg_left (hmgf _) (Real.exp_pos _).le)).trans ?_
    rw [← Real.exp_add]; refine Real.exp_le_exp.2 ?_
    rw [show -uR * ε + a * ((n : ℝ) + uR) ^ 2 = (n : ℝ) * ε - 2 * (ε ^ 2 / (8 * a)) by dsimp [uR]; field_simp; ring]
    simp only [neg_div]; linarith
  have hlower : (massPowerTilt μ m n).real {ω | m ω - 1 < -ε} ≤ Real.exp (-ε ^ 2 / (8 * a)) := by
    let SL := {ω | m ω - 1 < -ε}
    have hSL : MeasurableSet SL := measurableSet_lt (hm.sub measurable_const) measurable_const
    let uL := ε / (2 * a)
    have huL : 0 ≤ uL := div_nonneg he0 (by positivity)
    have hch : (massPowerTilt μ m n).real SL ≤ Real.exp (-uL * ε) * ∫ ω, Real.exp ((-uL) * (m ω - 1)) ∂μ := by
      rw [hreal SL hSL, ← integral_const_mul]
      refine integral_mono ((hI.div_const _).indicator hSL) ((hexpI (-uL)).const_mul _) fun ω => ?_
      by_cases hω : ω ∈ SL
      · simp only [Set.indicator_of_mem hω]
        have hm0 : 0 ≤ m ω := hl.le.trans (hbound ω).1
        have hh : m ω - 1 < -ε := hω
        refine (div_le_self (pow_nonneg hm0 n) hG).trans ((pow_le_one₀ hm0 (by linarith)).trans ?_)
        rw [← Real.exp_add]
        exact Real.one_le_exp_iff.2 (by nlinarith [mul_nonneg huL (sub_nonneg.2 hh.le)])
      · simp only [Set.indicator_of_notMem hω]; positivity
    refine (hch.trans (mul_le_mul_of_nonneg_left (hmgf _) (Real.exp_pos _).le)).trans ?_
    rw [← Real.exp_add]; refine Real.exp_le_exp.2 ?_
    rw [show -uL * ε + a * (-uL) ^ 2 = -2 * (ε ^ 2 / (8 * a)) by dsimp [uL]; field_simp; ring]
    simp only [neg_div]; linarith [div_nonneg (sq_nonneg ε) (by positivity : (0 : ℝ) ≤ 8 * a)]
  rw [show {ω | ε < |m ω - 1|} = {ω | ε < m ω - 1} ∪ {ω | m ω - 1 < -ε} by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_union, lt_abs]
    exact ⟨fun h => h.elim Or.inl fun h => Or.inr (by linarith),
           fun h => h.elim Or.inl fun h => Or.inr (by linarith)⟩]
  exact (measureReal_union_le _ _).trans (by linarith)

section TiltedAndAppend
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def highTiltedObservableMean {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (ν : Measure Ω) (n : ℕ) (a V : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (H : (Fin n → Observation d) → ℝ) : ℝ :=
  ∫ ω, ∫ z, H z ∂highRealSampleKernel n a V p F hp hF ω
    ∂massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n

section TiltedRegularity
variable {J : Type*} [Fintype J] [LinearOrder J]
    (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T Ba : ℝ) (hBa : 0 ≤ Ba)
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ) (hactivation : Measurable activation)
    (hcenter : ∫ e, activation e ∂π = 0) (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : T * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    {d : ℕ} (n : ℕ) (a v η aRaw bRaw : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (hmass : ∀ u ∈ Icc 0 T,
      (historyMarkedPrior dependent Δ u π activation).map (fun ω => highRawDensityMass (p ω)) =
      (historyMarkedPrior dependent Δ 0 π activation).map (fun ω => highRawDensityMass (p ω)))
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hHb : ∀ z, |H z| ≤ B)
include hrefl hsymm hΔ hlabels hBa hactivation hcenter habound hsmall ha haRaw hp hF hraw hq hmass hH hB hHb

lemma historyMarkedPrior_tiltedObservable_eq_raw (t : ℝ) (ht : t ∈ Icc 0 T) :
    highTiltedObservableMean (historyMarkedPrior dependent Δ t π activation)
      n a (v - η ^ 2 * t) p F hp hF H =
      (massPowerNormalizer (historyMarkedPrior dependent Δ 0 π activation)
        (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ ω, highRawObservable n a (v - η ^ 2 * t) (p ω) (F ω) H
          ∂historyMarkedPrior dependent Δ t π activation := by
  have hint : Integrable activation π := Integrable.of_bound hactivation.aestronglyMeasurable Ba
    (Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using habound e)
  have hs : t * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 hBa)
      (historyReferenceRho_pos Δ).le).trans hsmall
  let _ := historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels t Ba ht.1 hBa π
    activation hint hcenter habound hs
  rw [highTiltedObservableMean, massPowerTilt_highReal_observable_mean
    (historyMarkedPrior dependent Δ t π activation) n a (v - η ^ 2 * t) p F hp hF
      aRaw bRaw haRaw hraw ha.ne' (hq t ht) H hH B hB hHb,
    massPowerNormalizer_eq_of_massLaw _ _ _ (highRawDensityMass_joint_measurable p hp) n (hmass t ht)]

theorem historyMarkedPrior_tiltedObservable_hasDerivAt (t : ℝ) (ht : 0 < t) (htT : t < T) :
    HasDerivAt (fun u => highTiltedObservableMean (historyMarkedPrior dependent Δ u π activation)
      n a (v - η ^ 2 * u) p F hp hF H)
      ((massPowerNormalizer (historyMarkedPrior dependent Δ 0 π activation)
        (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ((-η ^ 2 * ∫ ω, highRawObservableVarianceDerivative n a (v - η ^ 2 * t) (p ω) (F ω) H
          ∂historyMarkedPrior dependent Δ t π activation) +
          historyMarkedPriorGenerator dependent hsymm Δ t π activation
            (fun ω => highRawObservable n a (v - η ^ 2 * t) (p ω) (F ω) H))) t := by
  let P := |bRaw|
  have hP : 0 ≤ P := abs_nonneg _
  have hpb (ω : HistoryMarked dependent E) (x : Covariate d) : |p ω x| ≤ P := by
    rw [abs_of_nonneg (haRaw.le.trans (hraw ω x).1)]
    exact (hraw ω x).2.trans (le_abs_self _)
  let G : ℝ → HistoryMarked dependent E → ℝ := fun u ω => highRawObservable n a (v - η ^ 2 * u) (p ω) (F ω) H
  let G' : ℝ → HistoryMarked dependent E → ℝ := fun u ω =>
    -η ^ 2 * highRawObservableVarianceDerivative n a (v - η ^ 2 * u) (p ω) (F ω) H
  let M : ℝ := B * P ^ n * (highSampleReference d n).real Set.univ
  let M' : ℝ := η ^ 2 * (B * (P ^ n * ((n : ℝ) / a ^ 2)) * (highSampleReference d n).real Set.univ)
  have hrawD : HasDerivAt (fun u => ∫ ω, G u ω ∂historyMarkedPrior dependent Δ u π activation)
      ((-η ^ 2 * ∫ ω, highRawObservableVarianceDerivative n a (v - η ^ 2 * t) (p ω) (F ω) H
        ∂historyMarkedPrior dependent Δ t π activation) +
        historyMarkedPriorGenerator dependent hsymm Δ t π activation (G t)) t := by
    simpa only [G, G', integral_const_mul] using
      historyMarkedPrior_observable_product_rule dependent hrefl hsymm Δ hΔ hlabels
        T Ba t ht htT hBa π activation hactivation habound hsmall G G'
        (fun u => highRawObservable_measurable n a (v - η ^ 2 * u) p F hp hF H hH)
        (fun u => (highRawObservableVarianceDerivative_measurable n a (v - η ^ 2 * u) p F hp hF H hH).const_mul (-η ^ 2))
        M M' (by dsimp [M]; positivity) (by dsimp [M']; positivity)
        (fun u hu ω => highRawObservable_abs_le n a (v - η ^ 2 * u) P B hP hB (p ω) (F ω) (hpb ω)
          ha.ne' (hq u ⟨hu.1.le, hu.2.le⟩ ω) H hHb)
        (fun u hu ω => by
          change |-η ^ 2 * highRawObservableVarianceDerivative n a (v - η ^ 2 * u) (p ω) (F ω) H| ≤ _
          rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg η)]
          exact mul_le_mul_of_nonneg_left (highRawObservableVarianceDerivative_abs_le n a (v - η ^ 2 * u)
            P B ha hP hB (p ω) (F ω) (hpb ω) (hq u ⟨hu.1.le, hu.2.le⟩ ω) H hHb) (sq_nonneg η))
        fun ω u hu => highRawObservable_hasDerivAt_path n a v η u T P B ha hu.1 hu.2 hP hB p F hp hF hpb
          (fun w hw => hq w ⟨hw.1.le, hw.2.le⟩) H hH hHb ω
  refine (hrawD.const_mul (massPowerNormalizer (historyMarkedPrior dependent Δ 0 π activation)
    (fun ω => highRawDensityMass (p ω)) n)⁻¹).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht htT] with u hu
  exact historyMarkedPrior_tiltedObservable_eq_raw dependent hrefl hsymm Δ hΔ hlabels T Ba hBa
    π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw hq hmass
    H hH B hB hHb u ⟨hu.1.le, hu.2.le⟩

theorem historyMarkedPrior_tiltedObservable_exists_lipschitz :
    ∃ K : NNReal, LipschitzOnWith K
      (fun u => highTiltedObservableMean (historyMarkedPrior dependent Δ u π activation)
        n a (v - η ^ 2 * u) p F hp hF H) (Icc 0 T) := by
  let P := |bRaw|
  have hP : 0 ≤ P := abs_nonneg _
  have hpb (ω : HistoryMarked dependent E) (x : Covariate d) : |p ω x| ≤ P := by
    rw [abs_of_nonneg (haRaw.le.trans (hraw ω x).1)]
    exact (hraw ω x).2.trans (le_abs_self _)
  let G : ℝ → HistoryMarked dependent E → ℝ := fun u ω => highRawObservable n a (v - η ^ 2 * u) (p ω) (F ω) H
  let c0 : ℝ := B * (η ^ 2 * (P ^ n * ((n : ℝ) / a ^ 2)))
  have hc0 : 0 ≤ c0 := by dsimp [c0]; positivity
  let K₀ : NNReal := ⟨c0 * (highSampleReference d n).real Set.univ, by positivity⟩
  have hGlip (ω : HistoryMarked dependent E) : LipschitzOnWith K₀ (fun u => G u ω) (Icc 0 T) := by
    let L : ℝ → ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ := fun u z =>
      H (encodeDesignResponse a z) * highRawSampleLikelihood n a (v - η ^ 2 * u) (p ω) (F ω) z
    have hLM (u : ℝ) : Measurable (L u) := by
      have hj : Measurable (Function.uncurry fun ω z =>
          highRawSampleLikelihood n a (v - η ^ 2 * u) (p ω) (F ω) z) :=
        highRawSampleLikelihood_joint_measurable n a (v - η ^ 2 * u) p F hp hF
      exact (hH.comp (encodeDesignResponse_measurable a)).mul hj.of_uncurry_left
    have hi (u : ℝ) (hu : u ∈ Icc 0 T) : Integrable (L u) (highSampleReference d n) :=
      Integrable.of_bound (hLM u).aestronglyMeasurable (B * P ^ n) <| Eventually.of_forall fun z => by
        change ‖H (encodeDesignResponse a z) * highRawSampleLikelihood n a (v - η ^ 2 * u) (p ω) (F ω) z‖ ≤ _
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hHb _) (highRawSampleLikelihood_abs_le n a (v - η ^ 2 * u) P hP
          (p ω) (F ω) (hpb ω) ha.ne' (hq u hu ω) z) (abs_nonneg _) hB
    have hl (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
        LipschitzOnWith ⟨c0, hc0⟩ (fun u => L u z) (Icc 0 T) := by
      refine (convex_Icc (0 : ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
        (fun u _ => ((highRawSampleLikelihood_hasDerivAt_path n a v η u (p ω) (F ω) z).const_mul
          (H (encodeDesignResponse a z))).hasDerivWithinAt) fun u hu => NNReal.coe_le_coe.1 ?_
      change ‖H (encodeDesignResponse a z) * (-η ^ 2 *
        highRawSampleVarianceDerivative n a (v - η ^ 2 * u) (p ω) (F ω) z)‖ ≤ c0
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg η)]
      exact mul_le_mul (hHb _) (mul_le_mul_of_nonneg_left
        (highRawSampleVarianceDerivative_abs_le n a (v - η ^ 2 * u) P ha hP
          (p ω) (F ω) (hpb ω) (hq u hu ω) z) (sq_nonneg η)) (by positivity) hB
    refine LipschitzOnWith.of_dist_le_mul fun u hu w hw => ?_
    change dist (∫ z, L u z ∂highSampleReference d n) (∫ z, L w z ∂highSampleReference d n) ≤
      c0 * (highSampleReference d n).real Set.univ * dist u w
    rw [dist_eq_norm, ← integral_sub (hi u hu) (hi w hw)]
    refine (norm_integral_le_of_norm_le_const (C := c0 * dist u w) <| Eventually.of_forall fun z => ?_).trans_eq (by ring)
    simpa only [dist_eq_norm] using (show dist (L u z) (L w z) ≤ c0 * dist u w from (hl z).dist_le_mul u hu w hw)
  let M : ℝ := B * P ^ n * (highSampleReference d n).real Set.univ
  obtain ⟨Kraw, hK⟩ : ∃ K : NNReal, LipschitzOnWith K
      (fun u => ∫ ω, G u ω ∂historyMarkedPrior dependent Δ u π activation) (Icc 0 T) :=
    ⟨_, historyMarkedPrior_variable_observable_lipschitz dependent hrefl hsymm Δ hΔ hlabels
      T Ba hBa π activation hactivation habound hsmall G
      (fun u => highRawObservable_measurable n a (v - η ^ 2 * u) p F hp hF H hH)
      M (by dsimp [M]; positivity)
      (fun u hu ω => highRawObservable_abs_le n a (v - η ^ 2 * u) P B hP hB (p ω) (F ω) (hpb ω) ha.ne' (hq u hu ω) H hHb)
      K₀ hGlip⟩
  let c : ℝ := (massPowerNormalizer (historyMarkedPrior dependent Δ 0 π activation)
    (fun ω => highRawDensityMass (p ω)) n)⁻¹
  refine ⟨⟨|c| * Kraw, mul_nonneg (abs_nonneg _) Kraw.coe_nonneg⟩, LipschitzOnWith.of_dist_le_mul fun u hu w hw => ?_⟩
  rw [historyMarkedPrior_tiltedObservable_eq_raw dependent hrefl hsymm Δ hΔ hlabels T Ba hBa
      π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw hq hmass H hH B hB hHb u hu,
    historyMarkedPrior_tiltedObservable_eq_raw dependent hrefl hsymm Δ hΔ hlabels T Ba hBa
      π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw hq hmass H hH B hB hHb w hw]
  change dist (c * _) (c * _) ≤ |c| * (Kraw : ℝ) * dist u w
  rw [Real.dist_eq, ← mul_sub, abs_mul]
  have hh := hK.dist_le_mul u hu w hw; rw [Real.dist_eq] at hh
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (abs_nonneg c)

end TiltedRegularity

section AppendLikelihood
variable {J : Type*} [Fintype J] [LinearOrder J]

def highAppendLikelihoodAction {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) (activation : E → ℝ) (n : ℕ) (a V : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ) (j : J)
    (ω : HistoryMarked dependent E) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  ∫ e, activation e * highRawSampleLikelihood n a V
    (p (historyMarkedAppend dependent hsymm j (ω, e)))
    (F (historyMarkedAppend dependent hsymm j (ω, e))) z ∂π

theorem highAppendLikelihoodAction_measurable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) [SFinite π] (activation : E → ℝ) (ha : Measurable activation) (n : ℕ) (a V : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) (j : J) :
    Measurable fun z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highAppendLikelihoodAction dependent hsymm π activation n a V p F j z.1 z.2 := by
  have hj : Measurable fun z :
      (HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3))) × E =>
      activation z.2 * highRawSampleLikelihood n a V
        (p (historyMarkedAppend dependent hsymm j (z.1.1, z.2)))
        (F (historyMarkedAppend dependent hsymm j (z.1.1, z.2))) z.1.2 :=
    (ha.comp measurable_snd).mul
      ((highRawSampleLikelihood_joint_measurable n a V p F hp hF).comp
        (((historyMarkedAppend_measurable dependent hsymm j).comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
          (measurable_snd.comp measurable_fst)))
  exact hj.stronglyMeasurable.integral_prod_right'.measurable

theorem highAppendLikelihoodAction_abs_le {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (activation : E → ℝ) (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V P : ℝ) (hP : 0 ≤ P) (ha : a ≠ 0)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : ∀ ω x, |p ω x| ≤ P) (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (j : J) (ω : HistoryMarked dependent E) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    |highAppendLikelihoodAction dependent hsymm π activation n a V p F j ω z| ≤ Ba * P^n := by
  rw [highAppendLikelihoodAction, ← Real.norm_eq_abs]
  have hb : ∀ e, ‖activation e * highRawSampleLikelihood n a V
      (p (historyMarkedAppend dependent hsymm j (ω, e)))
      (F (historyMarkedAppend dependent hsymm j (ω, e))) z‖ ≤ Ba * P^n := fun e => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (habound e) (highRawSampleLikelihood_abs_le n a V P hP _ _ (hp _) ha (hq _) z)
      (abs_nonneg _) hBa
  simpa using norm_integral_le_of_norm_le_const (μ := π) (Eventually.of_forall hb)

theorem highAppendLikelihoodAction_prior_observable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] (π : Measure E) [IsProbabilityMeasure π] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) [IsProbabilityMeasure ν]
    (activation : E → ℝ) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V P B : ℝ) (hP : 0 ≤ P) (hB : 0 ≤ B) (ha : a ≠ 0)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hpb : ∀ ω x, |p ω x| ≤ P) (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B)
    (j : J) :
    (∫ z : HistoryMarked dependent E × E, highRawObservable n a V
        (p (historyMarkedAppend dependent hsymm j z))
        (F (historyMarkedAppend dependent hsymm j z)) H * activation z.2 ∂ν.prod π) =
      ∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
        H (encodeDesignResponse a z.2) *
          highAppendLikelihoodAction dependent hsymm π activation n a V p F j z.1 z.2
            ∂ν.prod (highSampleReference d n) := by
  have hi : Integrable (fun z : HistoryMarked dependent E × E => highRawObservable n a V
      (p (historyMarkedAppend dependent hsymm j z))
      (F (historyMarkedAppend dependent hsymm j z)) H * activation z.2) (ν.prod π) :=
    Integrable.of_bound (((highRawObservable_measurable n a V p F hp hF H hH).comp
      (historyMarkedAppend_measurable dependent hsymm j)).mul (ham.comp measurable_snd)).aestronglyMeasurable
      ((B * P^n * (highSampleReference d n).real univ) * Ba) <| Eventually.of_forall fun z => by
        change ‖highRawObservable n a V (p (historyMarkedAppend dependent hsymm j z))
          (F (historyMarkedAppend dependent hsymm j z)) H * activation z.2‖ ≤ _
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (highRawObservable_abs_le n a V P B hP hB _ _ (hpb _) ha (hq _) H hHb)
          (habound _) (abs_nonneg _) (by positivity)
  have hi' : Integrable (fun z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      H (encodeDesignResponse a z.2) *
        highAppendLikelihoodAction dependent hsymm π activation n a V p F j z.1 z.2)
      (ν.prod (highSampleReference d n)) :=
    Integrable.of_bound (((hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd).mul
      (highAppendLikelihoodAction_measurable dependent hsymm π activation ham n a V p F hp hF j)).aestronglyMeasurable
      (B * (Ba * P^n)) <| Eventually.of_forall fun z => by
        change ‖H (encodeDesignResponse a z.2) *
          highAppendLikelihoodAction dependent hsymm π activation n a V p F j z.1 z.2‖ ≤ _
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hHb _) (highAppendLikelihoodAction_abs_le π dependent hsymm activation Ba hBa
          habound n a V P hP ha p F hpb hq j z.1 z.2) (abs_nonneg _) hB
  rw [MeasureTheory.integral_prod _ hi, MeasureTheory.integral_prod _ hi']
  refine integral_congr_ae <| Eventually.of_forall fun ω => ?_
  have hM : Measurable fun z : E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      activation z.1 * (H (encodeDesignResponse a z.2) * highRawSampleLikelihood n a V
        (p (historyMarkedAppend dependent hsymm j (ω, z.1)))
        (F (historyMarkedAppend dependent hsymm j (ω, z.1))) z.2) :=
    (ham.comp measurable_fst).mul
      (((hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd).mul
        ((highRawSampleLikelihood_joint_measurable n a V p F hp hF).comp
          (((historyMarkedAppend_measurable dependent hsymm j).comp
            (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)))
  have hiω : Integrable (fun z : E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      activation z.1 * (H (encodeDesignResponse a z.2) * highRawSampleLikelihood n a V
        (p (historyMarkedAppend dependent hsymm j (ω, z.1)))
        (F (historyMarkedAppend dependent hsymm j (ω, z.1))) z.2))
      (π.prod (highSampleReference d n)) :=
    Integrable.of_bound hM.aestronglyMeasurable (Ba * (B * P^n)) <| Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul (habound _) (mul_le_mul (hHb _) (highRawSampleLikelihood_abs_le n a V P hP
        _ _ (hpb _) ha (hq _) z.2) (abs_nonneg _) hB) (by positivity) hBa
  calc
    (∫ e, highRawObservable n a V (p (historyMarkedAppend dependent hsymm j (ω, e)))
        (F (historyMarkedAppend dependent hsymm j (ω, e))) H * activation e ∂π)
      = ∫ e, ∫ z, activation e * (H (encodeDesignResponse a z) * highRawSampleLikelihood n a V
          (p (historyMarkedAppend dependent hsymm j (ω, e)))
          (F (historyMarkedAppend dependent hsymm j (ω, e))) z) ∂highSampleReference d n ∂π := by
        refine integral_congr_ae <| Eventually.of_forall fun e => ?_
        dsimp only; rw [mul_comm, highRawObservable, integral_const_mul]
    _ = ∫ z, ∫ e, activation e * (H (encodeDesignResponse a z) * highRawSampleLikelihood n a V
          (p (historyMarkedAppend dependent hsymm j (ω, e)))
          (F (historyMarkedAppend dependent hsymm j (ω, e))) z) ∂π ∂highSampleReference d n :=
        integral_integral_swap hiω
    _ = _ := integral_congr_ae <| Eventually.of_forall fun z => by
        dsimp only; rw [highAppendLikelihoodAction, ← integral_const_mul]
        exact integral_congr_ae <| Eventually.of_forall fun _ => by ring

end AppendLikelihood
end TiltedAndAppend
end ConcentrationAndTiltedLikelihood

end NearlyMinimax
