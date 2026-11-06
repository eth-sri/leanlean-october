module
public import NearlyMinimax.SpatialPairProductIntegration
public import Mathlib.Algebra.Order.Chebyshev
public import NearlyMinimax.SpatialSubsetEnergy
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import NearlyMinimax.HigherBandActivityConversion
public import NearlyMinimax.HighSourceCountCancellation
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace NearlyMinimax
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section
section
variable {d j k : ℕ} {lo hi : ℝ}
def boundedHyperplaneSpatialMoment (d ) (T : ℝ) (j )
    (U : Fin j → Covariate d) : ℝ :=
  ∫ z, ∏ l, boundedHyperplaneFieldValue z (U l) ∂boundedHyperplaneFieldLaw d T
theorem boundedHyperplaneSpatialMoment_measurable (d ) [NeZero d] (T j) :
    Measurable (boundedHyperplaneSpatialMoment d T j) := by
  have hm : Measurable (fun Uz : (Fin j → Covariate d) × partitionFieldMark (Covariate d × ℝ) =>
      ∏ l, boundedHyperplaneFieldValue Uz.2 (Uz.1 l)) :=
    Finset.measurable_prod _ (fun l _ =>
      (boundedHyperplaneFieldValue_measurable d).comp
        (measurable_snd.prodMk ((measurable_pi_apply l).comp measurable_fst)))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable
theorem boundedHyperplaneSpatialMoment_abs_le_one (d ) [NeZero d]
    (T j U) :
    |boundedHyperplaneSpatialMoment d T j U| ≤ 1 := by
  calc
    _ ≤ ∫ z, |∏ l, boundedHyperplaneFieldValue z (U l)| ∂boundedHyperplaneFieldLaw d T :=
      abs_integral_le_integral_abs
    _ = 1 := by simp only [Finset.abs_prod, boundedHyperplaneFieldValue_abs,
      Finset.prod_const_one, integral_const, probReal_univ, smul_eq_mul, one_mul]
def spatialQuadDistance  (q : CellMomentQuadruple j)
    (U : Fin j → Covariate d) : ℝ :=
  exactEuclideanDistance (U (q.val 0)) (U (q.val 1)) +
    exactEuclideanDistance (U (q.val 2)) (U (q.val 3))
theorem spatialQuadDistance_nonneg  (q : CellMomentQuadruple j)
    (U : Fin j → Covariate d) : 0 ≤ spatialQuadDistance q U :=
  add_nonneg (exactEuclideanDistance_nonneg _ _) (exactEuclideanDistance_nonneg _ _)
theorem spatialQuadDistance_continuous  (q : CellMomentQuadruple j) :
    Continuous (spatialQuadDistance (d := d) q) := by
  have hm01 : Continuous (fun U : Fin j → Covariate d => (U (q.val 0), U (q.val 1))) :=
    (continuous_apply (q.val 0)).prodMk (continuous_apply (q.val 1))
  have hm23 : Continuous (fun U : Fin j → Covariate d => (U (q.val 2), U (q.val 3))) :=
    (continuous_apply (q.val 2)).prodMk (continuous_apply (q.val 3))
  have h01 : Continuous (fun U : Fin j → Covariate d =>
      exactEuclideanDistance (U (q.val 0)) (U (q.val 1))) := by
    simpa only [Function.comp_def] using (exactEuclideanDistance_continuous (d := d)).comp hm01
  have h23 : Continuous (fun U : Fin j → Covariate d =>
      exactEuclideanDistance (U (q.val 2)) (U (q.val 3))) := by
    simpa only [Function.comp_def] using (exactEuclideanDistance_continuous (d := d)).comp hm23
  exact h01.add h23
theorem spatialPatchProbability_pi_ae_cube (d j : ℕ) :
    ∀ᵐ U ∂Measure.pi (fun _ : Fin j => spatialPatchProbability d),
      ∀ l, U l ∈ hyperplaneCube d := by
  apply ae_all_iff.mpr
  intro l
  have h_spatialPatchBox_eq_hyperplaneCube : spatialPatchBox d = hyperplaneCube d := by
    ext x
    simp only [spatialPatchBox, mem_Icc, Pi.le_def, hyperplaneCube, mem_ofPred_eq, abs_le]
    exact ⟨fun h r => ⟨h.1 r, h.2 r⟩, fun h => ⟨fun r => (h r).1, fun r => (h r).2⟩⟩
  exact (measurePreserving_eval (fun _ => spatialPatchProbability d) l).quasiMeasurePreserving.tendsto_ae.eventually
    (by rw [spatialPatchProbability, ← h_spatialPatchBox_eq_hyperplaneCube]; exact (ae_restrict_mem measurableSet_Icc).filter_mono (Measure.ae_smul_measure_le _))
theorem boundedHyperplaneSpatialMoment_squared_probability_integral_le
    (d ) [NeZero d] (T ) (hT : 0 < T) (j ) (hj : 4 ≤ j) :
    (∫ U : Fin j → Covariate d, (boundedHyperplaneSpatialMoment d T j U)^2
      ∂Measure.pi (fun _ : Fin j => spatialPatchProbability d)) ≤
      ↑j^8 * (spatialExponentialConstant d / T^d)^2 := by
  classical
  let π := spatialPatchProbability d
  let μ := Measure.pi (fun _ : Fin j => π)
  let a : ℝ := Fintype.card (CellMomentQuadruple j)
  let E : CellMomentQuadruple j → (Fin j → Covariate d) → ℝ :=
    fun q U => Real.exp (-(T * spatialQuadDistance q U))
  have hem (q : CellMomentQuadruple j) : Measurable (E q) :=
    (spatialQuadDistance_continuous q |>.const_mul T |>.neg |>.rexp).measurable
  have hei (q : CellMomentQuadruple j) : Integrable (E q) μ :=
    Integrable.of_bound (hem q).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun U => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hT.le (spatialQuadDistance_nonneg q U))))
  have hmi : Integrable (fun U => (boundedHyperplaneSpatialMoment d T j U)^2) μ :=
    Integrable.of_bound ((boundedHyperplaneSpatialMoment_measurable d T j).pow_const 2).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun U => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [boundedHyperplaneSpatialMoment_abs_le_one d T j U, abs_nonneg (boundedHyperplaneSpatialMoment d T j U),
          sq_abs (boundedHyperplaneSpatialMoment d T j U)])
  have hpoint : ∀ᵐ U ∂μ, (boundedHyperplaneSpatialMoment d T j U)^2 ≤ a * ∑ q, E q U := by
    filter_upwards [spatialPatchProbability_pi_ae_cube d j] with U hU
    have h_boundedHyperplaneField_higher_moment_envelope : |∫ z, ∏ l, boundedHyperplaneFieldValue z (U l) ∂boundedHyperplaneFieldLaw d T| ≤
      ∑ q : CellMomentQuadruple j, Real.exp (-T / 2 *
        (euclideanNorm (fun r => U (q.val 0) r - U (q.val 1) r) +
          euclideanNorm (fun r => U (q.val 2) r - U (q.val 3) r))) := by
      have hb := poissonCellField_product_moment_abs_le_two_pairs (gaussianHyperplaneLaw d)
        (Real.toNNReal (2 * d * T)) hyperplaneHalfspace hyperplaneHalfspace_measurable j hj U
      apply hb.trans_eq
      apply Finset.sum_congr rfl
      intro q _
      rw [gaussianHyperplaneLaw_same_complement, gaussianHyperplaneLaw_same_complement,
        gaussianHyperplaneLaw_separation_real d _ _ (hU _) (hU _),
        gaussianHyperplaneLaw_separation_real d _ _ (hU _) (hU _),
        Real.coe_toNNReal (2 * ↑d * T) (by positivity)]
      congr 1
      have : ↑d ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
      field_simp
    have hb := h_boundedHyperplaneField_higher_moment_envelope
    simp_rw [← exactEuclideanDistance_eq_euclideanNorm] at hb
    change |boundedHyperplaneSpatialMoment d T j U| ≤
      ∑ q : CellMomentQuadruple j, Real.exp (-T / 2 * spatialQuadDistance q U) at hb
    have : 0 ≤ ∑ q : CellMomentQuadruple j, Real.exp (-T / 2 * spatialQuadDistance q U) :=
      Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
    have hs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun q : CellMomentQuadruple j => Real.exp (-T / 2 * spatialQuadDistance q U))
    have hsq : (boundedHyperplaneSpatialMoment d T j U)^2 ≤
        (∑ q : CellMomentQuadruple j, Real.exp (-T / 2 * spatialQuadDistance q U))^2 := by
      nlinarith [sq_abs (boundedHyperplaneSpatialMoment d T j U), abs_nonneg (boundedHyperplaneSpatialMoment d T j U)]
    have heq (q : CellMomentQuadruple j) :
        Real.exp (-T / 2 * spatialQuadDistance q U)^2 = E q U := by
      rw [← Real.exp_nat_mul]
      apply congrArg Real.exp
      ring
    exact hsq.trans (by simpa only [Finset.card_univ, heq, a] using hs)
  have hpair (q : CellMomentQuadruple j) : (∫ U, E q U ∂μ) ≤ (spatialExponentialConstant d / T^d)^2 := by
    have h_spatialPi_two_pairs_integral_factor {J} [Fintype J] (q : Fin 4 ↪ J) : (∫ U : J → Covariate d,
        Real.exp (-(T * (exactEuclideanDistance (U (q 0)) (U (q 1)) +
          exactEuclideanDistance (U (q 2)) (U (q 3))))) ∂Measure.pi (fun _ : J => π)) =
        (∫ xy : Covariate d × Covariate d, Real.exp (-(T * exactEuclideanDistance xy.1 xy.2)) ∂π.prod π)^2 := by
      have hpair : Measurable (fun xy : Covariate d × Covariate d => Real.exp (-(T*exactEuclideanDistance xy.1 xy.2))) :=
        (exactEuclideanDistance_continuous (d := d) |>.const_mul T |>.neg |>.rexp).measurable
      have he := spatialPi_two_pair_functions_factor π q _ hpair
      simp_rw [← Real.exp_add] at he
      simp_rw [show ∀ a b : ℝ, -(T*a) + -(T*b) = -(T*(a+b)) by intros; ring] at he
      exact he
    rw [show (∫ U, E q U ∂μ) =
        (∫ xy : Covariate d × Covariate d, Real.exp (-(T*exactEuclideanDistance xy.1 xy.2)) ∂π.prod π)^2 from
      (h_spatialPi_two_pairs_integral_factor ⟨q.val,q.property⟩)]
    have h_spatialPatchProbability_le_volume : spatialPatchProbability d ≤ volume := by
      intro S
      rw [spatialPatchProbability, Measure.smul_apply, smul_eq_mul]
      exact (mul_le_of_le_one_left (show 0 ≤ (volume.restrict (spatialPatchBox d)) S from zero_le) (ENNReal.inv_le_one.mpr (one_le_pow₀ (by norm_num)))).trans (Measure.restrict_le_self S)
    have h_spatial_probability_pair_exponential_integral_le (hd : 0 < d) : (∫ xy : Covariate d × Covariate d, Real.exp (-(T * exactEuclideanDistance xy.1 xy.2)) ∂π.prod π) ≤
        spatialExponentialConstant d / T^d := by
      have hi : Integrable (fun xy =>
          Real.exp (-(T * exactEuclideanDistance xy.1 xy.2))) (π.prod π) :=
        Integrable.of_bound ((exactEuclideanDistance_continuous (d := d) |>.const_mul T |>.neg |>.rexp).measurable).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun xy => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hT.le (exactEuclideanDistance_nonneg _ _))))
      rw [integral_prod _ hi]
      have hb (x : Covariate d) :
          (∫ y, Real.exp (-(T*exactEuclideanDistance x y)) ∂π) ≤ spatialExponentialConstant d / T^d :=
        (integral_mono_measure h_spatialPatchProbability_le_volume (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
          (exactEuclideanDistance_exponential_integrable hd hT x)).trans_eq
            (exactEuclideanDistance_exponential_integral hd hT x)
      simpa only [integral_const, probReal_univ, one_smul] using
        integral_mono hi.integral_prod_left (integrable_const _) hb
    have := (h_spatial_probability_pair_exponential_integral_le (NeZero.pos d))
    have : 0 ≤ ∫ xy : Covariate d × Covariate d, Real.exp (-(T*exactEuclideanDistance xy.1 xy.2)) ∂π.prod π :=
      integral_nonneg (fun _ => (Real.exp_pos _).le)
    nlinarith
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hac : a ≤ ↑j^4 := by
    have h_cellMomentQuadruple_card_le : Fintype.card (CellMomentQuadruple j) ≤ j^4 := by
      simpa only [Fintype.card_fun, Fintype.card_fin] using
        Fintype.card_subtype_le (fun q : Fin 4 → Fin j => Function.Injective q)
    dsimp [a]
    exact_mod_cast h_cellMomentQuadruple_card_le
  calc
    _ ≤ ∫ U, a * ∑ q, E q U ∂μ :=
      integral_mono_ae hmi ((integrable_finsetSum _ (fun q _ => hei q)).const_mul a) hpoint
    _ = a * ∑ q, ∫ U, E q U ∂μ := by
      rw [integral_const_mul, integral_finsetSum _ (fun q _ => hei q)]
    _ ≤ a * ∑ _q : CellMomentQuadruple j, (spatialExponentialConstant d / T^d)^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q _ => hpair q)) ha
    _ = a^2 * (spatialExponentialConstant d / T^d)^2 := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, a]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa only [← pow_mul] using pow_le_pow_left₀ ha hac 2) (sq_nonneg _)
theorem spatialPatchVolume_eq_smulProbability (d ) :
    volume.restrict (spatialPatchBox d) = (2 : ℝ≥0∞)^d • spatialPatchProbability d := by
  rw [spatialPatchProbability, smul_smul, ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_smul]
def hyperplaneSpatialMomentConstant (d : ℕ) : ℝ :=
  2^d * (1 + spatialExponentialConstant d)
theorem hyperplaneSpatialMomentConstant_positive (d ) :
    0 < hyperplaneSpatialMomentConstant d := by
  unfold hyperplaneSpatialMomentConstant
  have := spatialExponentialConstant_nonneg d
  positivity
theorem boundedHyperplaneSpatialMoment_L2_le
    (d ) [NeZero d] (T ) (hT : 0 < T) (j ) (hj : 4 ≤ j) :
    Real.sqrt (∫ U : Fin j → Covariate d, (boundedHyperplaneSpatialMoment d T j U)^2
      ∂Measure.pi (fun _ => volume.restrict (spatialPatchBox d))) ≤
      (hyperplaneSpatialMomentConstant d)^j * j^4 / T^d := by
  let C := spatialExponentialConstant d
  have hC  := spatialExponentialConstant_nonneg d
  have hC1 : 1 ≤ 1+C := by linarith
  have hCp : C^2 ≤ (1+C)^(2*j) := by
    calc C^2 ≤ (1+C)^2 := pow_le_pow_left₀ hC (by linarith) 2
         _ ≤ _ := pow_le_pow_right₀ hC1 (by omega)
  have hconstant : 2^(d*j) * C^2 ≤ (hyperplaneSpatialMomentConstant d)^(2*j) := by
    unfold hyperplaneSpatialMomentConstant
    rw [mul_pow]
    exact mul_le_mul (by rw [pow_mul]; exact pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (by omega)) hCp (sq_nonneg C) (by positivity)
  have h_boundedHyperplaneSpatialMoment_squared_cube_integral_le : (∫ U : Fin j → Covariate d, (boundedHyperplaneSpatialMoment d T j U)^2
      ∂Measure.pi (fun _ => volume.restrict (spatialPatchBox d))) ≤
      2^(d*j) * j^8 * (spatialExponentialConstant d / T^d)^2 := by
    let : IsFiniteMeasure ((2 : ℝ≥0∞)^d • spatialPatchProbability d) := by
      rw [← spatialPatchVolume_eq_smulProbability]
      infer_instance
    have he : Measure.pi (fun _ : Fin j => volume.restrict (spatialPatchBox d)) =
        ((2 : ℝ≥0∞)^d)^j • Measure.pi (fun _ : Fin j => spatialPatchProbability d) := by
      simp only [spatialPatchVolume_eq_smulProbability]
      simpa only [Fintype.card_fin] using spatialPi_const_smul (J := Fin j) (spatialPatchProbability d) ((2 : ℝ≥0∞)^d)
    rw [he, integral_smul_measure]
    simp only [ENNReal.toReal_pow, ENNReal.toReal_ofNat, smul_eq_mul, ← pow_mul]
    have hb := boundedHyperplaneSpatialMoment_squared_probability_integral_le d T hT j hj
    convert mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (2 : ℝ)^(d*j)) using 1; ring
  exact Real.sqrt_le_iff.mpr ⟨by positivity [hyperplaneSpatialMomentConstant_positive d], (h_boundedHyperplaneSpatialMoment_squared_cube_integral_le).trans (by have ht := mul_le_mul_of_nonneg_right hconstant (show 0 ≤ (j : ℝ)^8 / (T^d)^2 by positivity); convert ht using 1 <;> simp only [div_pow, mul_pow, ← pow_mul] <;> ring)⟩
theorem boundedHyperplaneSpatialMoment_joint_measurable (d j : ℕ) [NeZero d] :
    Measurable (fun z : ℝ × (Fin j → Covariate d) => boundedHyperplaneSpatialMoment d z.1 j z.2) := by
  let κ : Kernel (ℝ × (Fin j → Covariate d)) (FinePairFieldMark d) := (finePairFieldKernel d).comap (Prod.fst : ℝ × (Fin j → Covariate d) → ℝ) measurable_fst
  have hm : Measurable (fun z : (ℝ × (Fin j → Covariate d)) × FinePairFieldMark d =>
      ∏ l, boundedHyperplaneFieldValue z.2 (z.1.2 l)) :=
    Finset.measurable_prod _ (fun l _ => (boundedHyperplaneFieldValue_measurable d).comp
      (measurable_snd.prodMk ((measurable_pi_apply l).comp (measurable_snd.comp measurable_fst))))
  exact (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable
def fineFieldScaleWeight (d : ℕ) (T : ℝ) : ℝ := T / T ^ d
theorem fineFieldScaleWeight_continuousOn   (hlo : 0 < lo) :
    ContinuousOn (fineFieldScaleWeight d) (Icc lo hi) := by
  apply continuousOn_id.div (continuous_pow d).continuousOn
  intro T hT
  exact (pow_pos (hlo.trans_le hT.1) d).ne'
theorem fineFieldScaleWeight_eq_rpow   (hT : 0 < T) :
    fineFieldScaleWeight d T = T ^ (1 - (d : ℝ)) := by
  unfold fineFieldScaleWeight
  rw [Real.rpow_sub hT, Real.rpow_one, Real.rpow_natCast]
theorem weighted_scale_square_energy_le  [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (d : ℕ) {lo hi K : ℝ}
    (hlo : 0 < lo) (hK : 0 ≤ K) (F : ℝ × X → ℝ) (hF : Measurable F)
    (hFb : ∀ z, |F z| ≤ 1)
    (hE : ∀ T ∈ Icc lo hi, (∫ x, F (T,x) ^ 2 ∂mu) ≤ K ^ 2 / (T ^ d) ^ 2) :
    Integrable (fun x => (∫ T in Icc lo hi, T * F (T,x)) ^ 2) mu ∧
      (∫ x, (∫ T in Icc lo hi, T * F (T,x)) ^ 2 ∂mu) ≤
        K ^ 2 * (∫ T in Icc lo hi, fineFieldScaleWeight d T) ^ 2 := by
  let nu : Measure ℝ := volume.restrict (Icc lo hi)
  let W : ℝ := ∫ T, fineFieldScaleWeight d T ∂nu
  let f : ℝ × X → ℝ := fun z => z.1 * F z
  let g : ℝ × X → ℝ := fun z => z.1 * z.1 ^ d * F z ^ 2
  have hw : Integrable (fineFieldScaleWeight d) nu := ((fineFieldScaleWeight_continuousOn hlo).integrableOn_compact isCompact_Icc)
  have hW : 0 ≤ W := integral_nonneg_of_ae (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
    exact div_nonneg (hlo.le.trans hT.1) (pow_nonneg (hlo.le.trans hT.1) _))
  have hfi : Integrable f (nu.prod mu) :=
    ((continuous_id.continuousOn.integrableOn_compact isCompact_Icc).comp_fst mu).mul_bdd
      hF.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hFb z)
  have hgi : Integrable g (nu.prod mu) := by
    have ht : Integrable (fun T => T * T ^ d) nu :=
      (continuous_id.mul (continuous_pow d)).continuousOn.integrableOn_compact isCompact_Icc
    apply (ht.comp_fst mu).mul_bdd (c := 1) (hF.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_sq]
      nlinarith only [hFb z, sq_abs (F z), abs_nonneg (F z)])
  have hcs : ∀ᵐ x ∂mu, (∫ T, f (T,x) ∂nu) ^ 2 ≤ W * ∫ T, g (T,x) ∂nu := by
    filter_upwards [hfi.prod_left_ae, hgi.prod_left_ae] with x hfx hgx
    apply integral_square_le_weight_mass_mul nu (fun T => f (T,x))
      (fineFieldScaleWeight d) (fun T => g (T,x)) hfx hw hgx
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
      exact div_nonneg (hlo.le.trans hT.1) (pow_nonneg (hlo.le.trans hT.1) _)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
      exact mul_nonneg (mul_nonneg (hlo.le.trans hT.1)
        (pow_nonneg (hlo.le.trans hT.1) _)) (sq_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
      have hp : T ^ d ≠ 0 := (pow_pos (hlo.trans_le hT.1) d).ne'
      dsimp [f, g, fineFieldScaleWeight]
      field_simp
      exact le_refl _
  have hsi : Integrable (fun x => (∫ T, f (T,x) ∂nu) ^ 2) mu := by
    apply (hgi.integral_prod_right.const_mul W).mono'
      ((measurable_fst.mul hF).stronglyMeasurable.integral_prod_left'.measurable.pow_const 2).aestronglyMeasurable
    filter_upwards [hcs] with x hx
    rw [Real.norm_eq_abs, abs_sq]
    exact hx
  have hbound := integral_mono_ae hsi (hgi.integral_prod_right.const_mul W) hcs
  rw [integral_const_mul] at hbound
  rw [(integral_integral_swap hgi).symm] at hbound
  have hm : (∫ T, ∫ x, g (T,x) ∂mu ∂nu) ≤ ∫ T, K ^ 2 * fineFieldScaleWeight d T ∂nu := by
    apply integral_mono_ae hgi.integral_prod_left (hw.const_mul (K ^ 2))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
    dsimp [g]
    rw [integral_const_mul]
    have hp : 0 < T := hlo.trans_le hT.1
    have h := mul_le_mul_of_nonneg_left (hE T hT)
      (mul_nonneg hp.le (pow_nonneg hp.le d))
    apply h.trans_eq
    dsimp [fineFieldScaleWeight]
    field_simp
  refine ⟨hsi, ?_⟩
  convert (hbound.trans (mul_le_mul_of_nonneg_left (hm.trans_eq (integral_const_mul _ _)) hW)) using 1 <;> dsimp [f, W, nu] <;> ring
theorem finePairTimeSubsetMoment_univ_eq  [NeZero d]
    (lo hi U) :
    finePairTimeSubsetMoment lo hi U Finset.univ =
      ∫ T in Icc lo hi, T * boundedHyperplaneSpatialMoment d T j U := by
  rw [finePairTimeSubsetMoment_actual]
  rfl
theorem finePairTimeSubsetMoment_univ_square_integrable  [NeZero d]
    (hd : 3 ≤ d) (hj : 4 ≤ j)  (hlo : 0 < lo) :
    Integrable (fun U : Fin j → Covariate d =>
      finePairTimeSubsetMoment lo hi U Finset.univ ^ 2) (fullSpatialPatchDesign d j) := by
  let K : ℝ := hyperplaneSpatialMomentConstant d ^ j * ↑j ^ 4
  have hK : 0 ≤ K := by positivity [hyperplaneSpatialMomentConstant_positive d]
  have hh := weighted_scale_square_energy_le (fullSpatialPatchDesign d j) d (lo := lo) (hi := hi) (K := K) hlo hK
    (fun z => boundedHyperplaneSpatialMoment d z.1 j z.2)
    (boundedHyperplaneSpatialMoment_joint_measurable d j)
    (fun z => boundedHyperplaneSpatialMoment_abs_le_one d z.1 j z.2) (fun T hT => by
      have hp : 0 < T := hlo.trans_le hT.1
      have hb := boundedHyperplaneSpatialMoment_L2_le d T hp j hj
      have hn : 0 ≤ ∫ U : Fin j → Covariate d,
          boundedHyperplaneSpatialMoment d T j U ^ 2 ∂fullSpatialPatchDesign d j :=
        integral_nonneg (fun _ => sq_nonneg _)
      have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ K / T ^ d)).mpr hb
      change Real.sqrt (∫ U : Fin j → Covariate d,
        boundedHyperplaneSpatialMoment d T j U ^ 2 ∂fullSpatialPatchDesign d j) ^ 2 ≤
          (K / T ^ d) ^ 2 at hs
      simpa only [Real.sq_sqrt hn, div_pow] using hs)
  simp_rw [finePairTimeSubsetMoment_univ_eq]
  exact hh.1
theorem finePairTimeSubsetMoment_univ_L2_le  [NeZero d]
    (hd : 3 ≤ d) (hj : 4 ≤ j)  (hlo : 0 < lo) :
    Real.sqrt (∫ U : Fin j → Covariate d,
      finePairTimeSubsetMoment lo hi U Finset.univ ^ 2 ∂fullSpatialPatchDesign d j) ≤
      hyperplaneSpatialMomentConstant d ^ j * ↑j ^ 4 * lo ^ (2 - (d : ℝ)) := by
  let K : ℝ := hyperplaneSpatialMomentConstant d ^ j * (j : ℝ) ^ 4
  have hK : 0 ≤ K := by positivity [hyperplaneSpatialMomentConstant_positive d]
  have hh := weighted_scale_square_energy_le (fullSpatialPatchDesign d j) d (lo := lo) (hi := hi) (K := K) hlo hK
    (fun z => boundedHyperplaneSpatialMoment d z.1 j z.2)
    (boundedHyperplaneSpatialMoment_joint_measurable d j)
    (fun z => boundedHyperplaneSpatialMoment_abs_le_one d z.1 j z.2) (fun T hT => by
      have hp : 0 < T := hlo.trans_le hT.1
      have hb := boundedHyperplaneSpatialMoment_L2_le d T hp j hj
      have hn : 0 ≤ ∫ U : Fin j → Covariate d,
          boundedHyperplaneSpatialMoment d T j U ^ 2 ∂fullSpatialPatchDesign d j :=
        integral_nonneg (fun _ => sq_nonneg _)
      have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ K / T ^ d)).mpr hb
      change Real.sqrt (∫ U : Fin j → Covariate d,
        boundedHyperplaneSpatialMoment d T j U ^ 2 ∂fullSpatialPatchDesign d j) ^ 2 ≤
          (K / T ^ d) ^ 2 at hs
      simpa only [Real.sq_sqrt hn, div_pow] using hs)
  have h_fineFieldScaleWeight_integral_le : (∫ T in Icc lo hi, fineFieldScaleWeight d T) ≤ lo ^ (2 - (d : ℝ)) / (d - 2 : ℝ) := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hdec : (1 : ℝ) - d < -1 := by linarith only [hdR]
    have he : (∫ T in Icc lo hi, fineFieldScaleWeight d T) =
        ∫ T in Icc lo hi, T ^ (1 - (d : ℝ)) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro T hT
      exact fineFieldScaleWeight_eq_rpow (hlo.trans_le hT.1)
    rw [he]
    apply (integral_mono_measure (Measure.restrict_mono_set volume Icc_subset_Ici_self)
      (by filter_upwards [ae_restrict_mem measurableSet_Ici] with T hT; exact Real.rpow_nonneg (hlo.le.trans hT) _) (by change Integrable (fun T : ℝ => T ^ (1 - (d : ℝ))) (volume.restrict (Ici lo)); rw [← Measure.restrict_congr_set Ioi_ae_eq_Ici]; exact integrableOn_Ioi_rpow_of_lt hdec hlo)).trans_eq
    rw [integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt hdec hlo]
    have he : (1 - (d : ℝ)) + 1 = 2 - (d : ℝ) := by ring
    rw [he, show (2 : ℝ) - d = -(d - 2 : ℝ) by ring]
    simp only [div_neg]
    ring
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (1 : ℝ) ≤ d - 2 := by linarith only [hdR]
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg hK (Real.rpow_nonneg hlo.le _), ?_⟩
  simp_rw [finePairTimeSubsetMoment_univ_eq]
  exact (hh.2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by apply integral_nonneg_of_ae; filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT; exact div_nonneg (hlo.le.trans hT.1) (pow_nonneg (hlo.le.trans hT.1) _)) ((h_fineFieldScaleWeight_integral_le).trans (div_le_self (Real.rpow_nonneg hlo.le _) hden)) 2) (sq_nonneg K))).trans_eq (mul_pow _ _ 2).symm
theorem finePairTimeSubsetMoment_reindex  (lo hi : ℝ)
    (U : Fin k → Covariate d) (S : Finset (Fin k)) :
    finePairTimeSubsetMoment lo hi U S =
      finePairTimeSubsetMoment lo hi (spatialSubsetConfiguration S U) Finset.univ := by
  unfold finePairTimeSubsetMoment
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun e => by
    change e.1 * (∏ i ∈ S, finePairTimeFieldValue e (U i)) =
      e.1 * (∏ j : Fin S.card, finePairTimeFieldValue e (spatialSubsetConfiguration S U j))
    have h_spatial_subset_product_reindex : (∏ i ∈ S, (finePairTimeFieldValue e) (U i)) = ∏ j : Fin S.card, (finePairTimeFieldValue e) (spatialSubsetConfiguration S U j) := by
      rw [← Finset.prod_coe_sort S (fun i => (finePairTimeFieldValue e) (U i))]
      exact (((Fintype.equivFin S).trans (finCongr (Fintype.card_coe S))).symm.prod_comp (fun i => (finePairTimeFieldValue e) (U i.val))).symm
    rw [h_spatial_subset_product_reindex])
theorem finePairTimeSubsetMoment_measurable  [NeZero d] (lo hi : ℝ)
    (S : Finset (Fin k)) :
    Measurable (fun U : Fin k → Covariate d => finePairTimeSubsetMoment lo hi U S) := by
  simp_rw [finePairTimeSubsetMoment_reindex (S := S)]
  have h_finePairTimeSubsetMoment_univ_measurable {j : ℕ} : Measurable (fun U : Fin j → Covariate d => finePairTimeSubsetMoment lo hi U Finset.univ) := by
    have h : Measurable (fun U =>
        ∫ T in Icc lo hi, T * boundedHyperplaneSpatialMoment d T j U) :=
      (measurable_fst.mul (boundedHyperplaneSpatialMoment_joint_measurable d j)).stronglyMeasurable.integral_prod_left'.measurable
    simp_rw [finePairTimeSubsetMoment_univ_eq]
    exact h
  exact h_finePairTimeSubsetMoment_univ_measurable.comp (spatialSubsetConfiguration_measurable S)
theorem finePairTimeSubsetMoment_square_integrable  [NeZero d]
    (hd : 3 ≤ d)  (hlo : 0 < lo) (S : Finset (Fin k)) (hS : 4 ≤ S.card) :
    Integrable (fun U : Fin k → Covariate d => finePairTimeSubsetMoment lo hi U S ^ 2)
      (fullSpatialPatchDesign d k) := by
  simp_rw [finePairTimeSubsetMoment_reindex (S := S)]
  exact spatial_subset_square_integrable_enumerated S
    (fun V => finePairTimeSubsetMoment lo hi V Finset.univ)
    (finePairTimeSubsetMoment_univ_square_integrable hd hS hlo)
theorem finePairTimeSubsetMoment_square_integral_reindex 
    (lo hi ) (S : Finset (Fin k)) :
    (∫ U : Fin k → Covariate d, finePairTimeSubsetMoment lo hi U S ^ 2
      ∂fullSpatialPatchDesign d k) = ↑2 ^ (d * (k - S.card)) *
        ∫ V : Fin S.card → Covariate d, finePairTimeSubsetMoment lo hi V Finset.univ ^ 2
          ∂fullSpatialPatchDesign d S.card := by
  simp_rw [finePairTimeSubsetMoment_reindex (S := S)]
  exact spatial_subset_square_integral_enumerated (d := d) S
    (fun V => finePairTimeSubsetMoment lo hi V Finset.univ)
def fineFieldSubsetEnergyBase (d : ℕ) : ℝ :=
  4 * (2 : ℝ) ^ d * hyperplaneSpatialMomentConstant d ^ 2
theorem finePairTimeSubsetMoment_uniform_square_integral_le  [NeZero d]
    (hd : 3 ≤ d)  (hlo : 0 < lo) (S : Finset (Fin k)) (hS : 4 ≤ S.card) :
    (∫ U : Fin k → Covariate d, finePairTimeSubsetMoment lo hi U S ^ 2
      ∂fullSpatialPatchDesign d k) ≤
      (2 : ℝ) ^ (d * k) * hyperplaneSpatialMomentConstant d ^ (2 * k) *
        (k : ℝ) ^ 8 * (lo ^ (2 - (d : ℝ))) ^ 2 := by
  have hc : S.card ≤ k := by
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ S)
  have hv : (2 : ℝ) ^ (d * (k - S.card)) ≤ (2 : ℝ) ^ (d * k) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left d (Nat.sub_le _ _))
  have h_hyperplaneSpatialMomentConstant_ge_one : 1 ≤ hyperplaneSpatialMomentConstant d := by
    unfold hyperplaneSpatialMomentConstant
    have hp : 1 ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    have hc := spatialExponentialConstant_nonneg d
    nlinarith only [hp, hc]
  have hconst : hyperplaneSpatialMomentConstant d ^ (2 * S.card) ≤
      hyperplaneSpatialMomentConstant d ^ (2 * k) :=
    pow_le_pow_right₀ h_hyperplaneSpatialMomentConstant_ge_one (Nat.mul_le_mul_left 2 hc)
  have hj : (S.card : ℝ) ^ 8 ≤ (k : ℝ) ^ 8 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hc) 8
  have h_finePairTimeSubsetMoment_square_integral_le : (∫ U : Fin k → Covariate d, finePairTimeSubsetMoment lo hi U S ^ 2
      ∂fullSpatialPatchDesign d k) ≤
      (2 : ℝ) ^ (d * (k - S.card)) *
        (hyperplaneSpatialMomentConstant d ^ S.card * (S.card : ℝ) ^ 4 * lo ^ (2 - (d : ℝ))) ^ 2 := by
    rw [finePairTimeSubsetMoment_square_integral_reindex]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity [hyperplaneSpatialMomentConstant_positive d])).mpr (finePairTimeSubsetMoment_univ_L2_le (d := d) hd hS (hi := hi) hlo)
    simpa only [Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))] using hs
  have h := h_finePairTimeSubsetMoment_square_integral_le
  apply h.trans
  have hC := (hyperplaneSpatialMomentConstant_positive d).le
  have h2 := mul_le_mul hv hconst (pow_nonneg hC _) (by positivity)
  have h3 := mul_le_mul h2 hj (pow_nonneg (Nat.cast_nonneg S.card) 8)
    (mul_nonneg (by positivity) (pow_nonneg hC _))
  have hh := mul_le_mul_of_nonneg_right h3 (sq_nonneg (lo ^ (2 - (d : ℝ))))
  convert hh using 1 <;> simp only [mul_pow, ← pow_mul] <;> ring
theorem finePairTimeSubsetMoment_sum_abs_square_integral_le  [NeZero d]
    (hd : 3 ≤ d)  (hlo : 0 < lo) (s : Finset (Finset (Fin k)))
    (hs : ∀ S ∈ s, 4 ≤ S.card) :
    (∫ U : Fin k → Covariate d, (∑ S ∈ s, |finePairTimeSubsetMoment lo hi U S|) ^ 2
      ∂fullSpatialPatchDesign d k) ≤
      fineFieldSubsetEnergyBase d ^ k * (k : ℝ) ^ 8 * (lo ^ (2 - (d : ℝ))) ^ 2 := by
  let K : ℝ := (2 : ℝ) ^ (d * k) * hyperplaneSpatialMomentConstant d ^ (2 * k) *
    (k : ℝ) ^ 8 * (lo ^ (2 - (d : ℝ))) ^ 2
  have hK : 0 ≤ K := by
    have := (hyperplaneSpatialMomentConstant_positive d).le
    positivity
  have h := finite_sum_square_integral_le (fullSpatialPatchDesign d k) s
    (fun S U => |finePairTimeSubsetMoment lo hi U S|) K
    (fun S _ => (finePairTimeSubsetMoment_measurable lo hi S).abs)
    (fun S hS => by simpa only [sq_abs] using finePairTimeSubsetMoment_square_integrable hd hlo S (hs S hS))
    (fun S hS => by simpa only [sq_abs] using finePairTimeSubsetMoment_uniform_square_integral_le hd hlo S (hs S hS))
  have hsub : s ⊆ (Finset.univ : Finset (Fin k)).powerset := by intro S _; simp
  have hc : (s.card : ℝ) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (by simpa only [Finset.card_powerset, Finset.card_univ, Fintype.card_fin] using Finset.card_le_card hsub)) 2
  have hh := mul_le_mul_of_nonneg_right hc hK
  apply (h.trans hh).trans_eq
  dsimp [K, fineFieldSubsetEnergyBase]
  simp only [mul_pow, pow_mul]
  have hfour : (4 : ℝ) ^ k = (2 : ℝ) ^ (k * 2) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, Nat.mul_comm]
  rw [hfour]
  ring
end
variable {d n F : ℕ} {T lam : ℝ}
def finePairResponseActionBudget (d q : ℕ) (C a ρ : ℝ) : ℝ :=
  512 * d * C^2 * (∑ j : Fin (2*q+2), |responseWeight q j|) * highSeparatedDerivativeBudget a ρ
def finePairDensityCoefficientBudget (ad bd : ℝ) (M n : ℕ) : ℝ :=
  |finePairDensityPrefactor ad bd| * bd^n *
    Real.cosh ((M+2 : ℕ) * exteriorTau ((ad+bd)/(bd-ad)))
theorem finePairDensityCoefficientBudget_nonneg (ad bd : ℝ) (hbd : 0 ≤ bd) (M n : ℕ) :
    0 ≤ finePairDensityCoefficientBudget ad bd M n := mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hbd _)) (Real.cosh_pos _).le
theorem finePairCountCoefficient_product_bound 
    (ad bd : ℝ) (ha : 0 < ad) (hab : ad < bd) (M : ℕ)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd) (S : Finset (Fin n)) :
    |finePairCountCoefficient ad bd M n S.card * (∏ i ∈ S, p i)| ≤
      finePairDensityCoefficientBudget ad bd M n := by
  have hb  := ha.trans hab
  have hpabs (i : Fin n) : |p i| ≤ bd := by
    rw [abs_of_pos (ha.trans_le (hp i).1)]
    exact (hp i).2
  have hprod : |∏ i ∈ S, p i| ≤ bd^S.card := by
    rw [Finset.abs_prod]
    exact (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hpabs i)).trans_eq
      (Finset.prod_const _)
  have he : |finePairDensityPrefactor ad bd| *
      bd^(n-S.card) * ((bd-ad)/(4*bd))^S.card *
      Real.cosh ((M+2 : ℕ)*exteriorTau ((ad+bd)/(bd-ad))) * bd^S.card =
      finePairDensityCoefficientBudget ad bd M n * ((bd-ad)/(4*bd))^S.card := by
    unfold finePairDensityCoefficientBudget
    have hpow : bd^(n-S.card) * bd^S.card = bd^n := by
      rw [← pow_add, Nat.sub_add_cancel (by simpa using Finset.card_le_univ S)]
    calc
      _ = |finePairDensityPrefactor ad bd| * (bd^(n-S.card)*bd^S.card) *
        Real.cosh ((M+2 : ℕ)*exteriorTau ((ad+bd)/(bd-ad))) * ((bd-ad)/(4*bd))^S.card := by ring
      _ = _ := by rw [hpow]
  rw [abs_mul]
  have h_finePairCountCoefficient_abs_bound : |finePairCountCoefficient ad bd M n S.card| ≤
      |finePairDensityPrefactor ad bd| * bd ^ (n - S.card) * ((bd - ad) / (4 * bd)) ^ S.card *
        Real.cosh ((M + 2 : ℕ) * exteriorTau ((ad + bd) / (bd - ad))) := by
    have hb  := ha.trans hab
    have hterm (h : Fin (M + 3)) :
        |exteriorNode ad bd (M + 2) h ^ (n - S.card) *
          (densityMargin ad bd (exteriorNode ad bd (M + 2) h) / bd) ^ S.card| ≤
        bd ^ (n - S.card) * ((bd - ad) / (4 * bd)) ^ S.card := by
      have hz := exteriorNode_mem ad bd hab.le (M + 2) h
      have ht := densityMargin_bounds ad bd hab _ hz
      have ht0  := div_nonneg ht.1 hb.le
      have htle : densityMargin ad bd (exteriorNode ad bd (M + 2) h) / bd ≤ (bd - ad) / (4 * bd) := by
        exact (div_le_div_of_nonneg_right ht.2.2.2 hb.le).trans_eq (by ring)
      rw [abs_mul, abs_pow, abs_pow, abs_of_nonneg (ha.le.trans hz.1), abs_of_nonneg ht0]
      exact mul_le_mul (pow_le_pow_left₀ (ha.le.trans hz.1) hz.2 _)
        (pow_le_pow_left₀ ht0 htle _) (pow_nonneg ht0 _) (pow_nonneg hb.le _)
    unfold finePairCountCoefficient
    rw [abs_mul]
    apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)).trans
    calc
      _ ≤ |finePairDensityPrefactor ad bd| *
          ∑ h : Fin (M + 3), |exteriorWeight ad bd (M + 2) h| *
            (bd ^ (n - S.card) * ((bd - ad) / (4 * bd)) ^ S.card) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum
        intro h _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hterm h) (abs_nonneg _)
      _ = _ := by
        rw [← Finset.sum_mul, exterior_rule_variation ad bd ha hab (M + 2) (by omega)]
        ring
  apply (mul_le_mul h_finePairCountCoefficient_abs_bound hprod (abs_nonneg _) (by positivity)).trans
  rw [he]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (div_nonneg (sub_nonneg.mpr hab.le) (by positivity)) (by apply (div_le_one (by positivity : ↑0 < 4*bd)).mpr; linarith only [ha, hb]))
    (finePairDensityCoefficientBudget_nonneg ad bd hb.le M n)).trans_eq (mul_one _)
theorem highFrameProfile_abs_le_coefficients  (x )
    (hx : ∀ i, |x i| ≤ 2) (v : HighFrameIndex d F → ℝ) :
    |∑ γ, highFrameFeature x γ * v γ| ≤ ∑ γ, |v γ| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro γ _
  rw [abs_mul]
  have h_highFrameFeature_abs_le_one : |highFrameFeature x γ| ≤ 1 := by
    unfold highFrameFeature
    rw [Finset.abs_prod]
    apply Finset.prod_le_one₀
    · intro i _
      exact abs_nonneg _
    · intro i _
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (by rw [abs_div, show |(8 : ℝ)| = 8 by norm_num]; apply (div_le_one (by norm_num : (0 : ℝ) < 8)).mpr; exact (hx i).trans (by norm_num))
  exact (mul_le_mul_of_nonneg_right h_highFrameFeature_abs_le_one (abs_nonneg _)).trans_eq (one_mul _)
theorem highFrameProfile_abs_le_one  (C ) (hC : 1 ≤ C)
    (x : Covariate d) (hx : ∀ i, |x i| ≤ 2) (v : HighFrameIndex d F → ℝ)
    (hv : ∑ γ, |v γ| ≤ C⁻¹) :
    |∑ γ, highFrameFeature x γ * v γ| ≤ 1 :=
  (highFrameProfile_abs_le_coefficients x hx v).trans (hv.trans (inv_le_one_of_one_le₀ hC))
theorem highFrameCoefficientRegression_abs_le 
    (C η ρ : ℝ) (hC : 1 ≤ C) (hη : 0 ≤ η) (hηρ : η ≤ ρ/2)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (g w : Fin n → ℝ) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹) (i : Fin n) :
    |coefficientRegression η g w (fun i => highFrameFeature (U i)) c i| ≤ ρ := by
  have hterm : |η*w i*(∑ γ, highFrameFeature (U i) γ * c γ)| ≤ η := by
    rw [abs_mul]
    exact (mul_le_mul (by rw [abs_mul, abs_of_nonneg hη]; exact (mul_le_mul_of_nonneg_left (hw i) hη).trans_eq (mul_one _)) (highFrameProfile_abs_le_one C hC (U i) (hU i) c hc) (abs_nonneg _) hη).trans_eq (mul_one _)
  exact (abs_add_le _ _).trans (by linarith only [hg i, hterm, hηρ])
theorem fine_pair_filtered_sum_abs_bound  (s P) [DecidablePred P]
    (c H : I → ℝ) (R B K : ℝ) (hB : 0 ≤ B)
    (hc : ∀ i ∈ s, |c i| ≤ B) (hR : |R| ≤ K) :
    |∑ i ∈ s, c i * (if P i then 1 else 0) * H i * R| ≤
      B*K * ∑ i ∈ s, if P i then |H i| else 0 := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hP : P i
  · simp only [if_pos hP, mul_one]
    calc
      _ = |c i| * |R| * |H i| := by rw [abs_mul, abs_mul]; ring
      _ ≤ B*K * |H i| := mul_le_mul_of_nonneg_right
        (mul_le_mul (hc i hi) hR (abs_nonneg _) hB) (abs_nonneg _)
  · simp [hP]
section Actual
variable {d n F : ℕ}
theorem finePairDistance_response_bound_of_chart (q ) (hn : 1 ≤ n)
    (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (g w : Fin n → ℝ) (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3)
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y) :
    |responseMatrixAction q C (finePairDistanceMatrix d F) c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)| ≤
        finePairResponseActionBudget d q C a ρ * ↑n^2 * η^2 :=
  have h_finePairDistance_response_all_count_bound (hC : 0 < C) (hφ : ∀ v : HighFrameIndex d F → ℝ, (∑ γ, |v γ|) ≤ C⁻¹ → ∀ i, |∑ γ, highFrameFeature (U i) γ * v γ| ≤ 1) : |responseMatrixAction q C (finePairDistanceMatrix d F) c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)| ≤
        finePairResponseActionBudget d q C a ρ * ↑n^2 * η^2 := by
    have hh := high_response_matrix_all_count_bound q hn C a V η ρ hC ha hη hρ hηρ
      (finePairDistanceMatrix d F) g w (fun i => highFrameFeature (U i)) c y hc hg hw hφ hp
    have hA := finePairDistanceMatrix_l1_le d F
    have hnonneg : 0 ≤ (∑ j : Fin (2*q+2), |responseWeight q j|) *
        (4 * (((2*ρ+a)/a^2)^2 + 2/a^2) * ↑n^2 * η^2) := by positivity
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hA (by positivity : ↑0 ≤ 2*C^2)) hnonneg
    exact (hh.trans hmul).trans_eq (by
      unfold finePairResponseActionBudget highSeparatedDerivativeBudget
      ring)
  (h_finePairDistance_response_all_count_bound (lt_of_lt_of_le zero_lt_one hC) (fun v hv i => highFrameProfile_abs_le_one C hC (U i) (hU i) v hv))
end Actual
theorem finite_sum_abs_square_integrable  [MeasurableSpace X]
    (μ : Measure X) (s : Finset I) (f : I → X → ℝ)
    (hm : ∀ i ∈ s, Measurable (f i))
    (hi : ∀ i ∈ s, Integrable (fun x => f i x ^ 2) μ) :
    Integrable (fun x => (∑ i ∈ s, |f i x|)^2) μ := by
  apply ((integrable_finsetSum s hi).const_mul _).mono' ((Finset.measurable_sum s (fun i hi => (hm i hi).abs)).pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_sq]
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] using
      Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => 1) (fun i => |f i x|))
 def finePairEvenActionSpatialBudget (d n M q : ℕ) (ad bd C a ρ η T0 : ℝ) : ℝ :=
  (finePairDensityCoefficientBudget ad bd M n *
    finePairResponseActionBudget d q C a ρ * n^2 * η^2)^2 *
      fineFieldSubsetEnergyBase d ^ n * n^8 * (T0 ^ (2 - (d : ℝ)))^2
def cardinalWeightDefect  (i : Fin n) (lam T : ℝ)
    (U : Fin n → Covariate d) : ℝ := 1 - integratedCardinalWeight lam T U i
def cardinalDefectSquareBudget (d n : ℕ) (T : ℝ) : ℝ :=
  (16 * spatialUnaryIntegralConstant d) ^ (n - 1) *
    T ^ (-(d : ℝ)) * (1 + Real.log T) ^ (n - 2)
theorem cardinalWeightDefect_measurable  (i : Fin n) (lam : ℝ)
     (hT : 1 ≤ T) : Measurable (cardinalWeightDefect (d := d) i lam T) :=
  have h_integrated_cardinal_weight_continuous  := continuous_parametric_integral_of_continuous
      (by simp_rw [spatial_cardinal_weight_scale_product]; unfold spatialUnaryWeight spatialSquaredDistance; fun_prop) (spatial_scale_domain_isCompact i T hT)
  measurable_const.sub h_integrated_cardinal_weight_continuous.measurable
theorem cardinalWeightDefect_mem_unit  (i : Fin n) 
    (hlam : 0 ≤ lam) (T : ℝ) (U : Fin n → Covariate d) :
    cardinalWeightDefect i lam T U ∈ Icc ↑0 1 := by
  have h := integrated_cardinal_weight_mem_unit i lam T hlam U
  unfold cardinalWeightDefect
  constructor <;> linarith only [h.1, h.2]
theorem cardinalWeightDefect_square_integrable  (i ) 
    (hlam : 0 ≤ lam)  (hT : 1 ≤ T) :
    Integrable (fun U => cardinalWeightDefect i lam T U ^ 2) (fullSpatialPatchDesign d n) := by
  apply Integrable.of_bound ((cardinalWeightDefect_measurable i lam hT).pow_const 2).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun U => by
    rw [Real.norm_eq_abs, abs_sq]
    have h := cardinalWeightDefect_mem_unit i hlam T U
    nlinarith only [h.1, h.2])
theorem cardinalWeightDefect_joint_square_integrable  (i : Fin n) 
    (hlam : 0 ≤ lam)  (hT : 1 ≤ T) :
    Integrable (fun z : Covariate d × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalDefect i lam T z.1 z.2 ^ 2)
      ((volume.restrict (spatialPatchBox d)).prod (spatialPatchDesignMeasure i d)) := ((cardinalHeadSplit_measurePreserving i (volume.restrict (spatialPatchBox d))).symm).integrable_comp_of_integrable (cardinalWeightDefect_square_integrable i hlam hT)
theorem cardinalWeightDefect_full_square_integral_le  (hd : 0 < d)
    (hn : 2 ≤ n) (i )  (hT : 1 ≤ T) :
    (∫ U, cardinalWeightDefect i (spatialInterpolationLambda d) T U ^ 2
      ∂fullSpatialPatchDesign d n) ≤ ↑2 ^ d * cardinalDefectSquareBudget d n T := by
  have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  have hj := cardinalWeightDefect_joint_square_integrable (d := d) i hlam hT
  rw [fullSpatialPatchDesign_split i _]
  change (∫ z : Covariate d × (SpatialScaleIndex i → Covariate d),
    anchoredCardinalDefect i (spatialInterpolationLambda d) T z.1 z.2 ^ 2
      ∂(volume.restrict (spatialPatchBox d)).prod (spatialPatchDesignMeasure i d)) ≤ _
  rw [integral_prod _ hj]
  have hb : (fun x => ∫ Y, anchoredCardinalDefect i (spatialInterpolationLambda d) T x Y ^ 2
      ∂spatialPatchDesignMeasure i d) ≤ᵐ[volume.restrict (spatialPatchBox d)]
      (fun _ => cardinalDefectSquareBudget d n T) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hlam : 0 < spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
    have h_anchored_cardinal_tail_spatial_integral_bound : (∫ Y, (∫ t : SpatialScaleVector i in Ici 0 \ spatialScaleDomain i T,
        anchoredCardinalScaleWeight i (spatialInterpolationLambda d) x t Y)
        ∂spatialPatchDesignMeasure i d) ≤
        (16 * spatialUnaryIntegralConstant d) ^ (n - 1) *
          T ^ (-(d : ℝ)) * (1 + Real.log T) ^ (n - 2) := by
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
      have hjoint := anchored_cardinal_tail_joint_integrable i hlam T x
      rw [(integral_prod_symm _ hjoint).symm.trans (integral_prod _ hjoint)]
      have hpowint := (spatial_scale_complement_power_integrable hn i
        (by positivity : (0 : ℝ) < (d : ℝ) / 2) T).const_mul
          ((spatialUnaryIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i))
      have hdom : (fun t : SpatialScaleVector i =>
          ∫ Y, anchoredCardinalScaleWeight i (spatialInterpolationLambda d) x t Y ∂spatialPatchDesignMeasure i d) ≤ᵐ[
            volume.restrict (Ici 0 \ spatialScaleDomain i T)]
          (fun t => (spatialUnaryIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i) *
            ∏ j, (1 + t j) ^ (-(d : ℝ) / 2 - 1)) := by
        filter_upwards [ae_restrict_mem (measurableSet_Ici.diff (spatial_scale_domain_isClosed i T).measurableSet)] with t ht
        have h_anchored_cardinal_spatial_integral_product (lam : ℝ) (x : Covariate d) (t : SpatialScaleVector i) : (∫ Y, anchoredCardinalScaleWeight i lam x t Y ∂spatialPatchDesignMeasure i d) =
            ∏ j : SpatialScaleIndex i, ∫ y in spatialPatchBox d, spatialUnaryWeight lam (t j) x y := by
          simp_rw [anchored_cardinal_scale_product]
          exact integral_fintype_prod_eq_prod
            (fun (j : SpatialScaleIndex i) (y : Covariate d) => spatialUnaryWeight lam (t j) x y)
        rw [h_anchored_cardinal_spatial_integral_product]
        have h : (∏ j : SpatialScaleIndex i, ∫ y in spatialPatchBox d,
            spatialUnaryWeight (spatialInterpolationLambda d) (t j) x y) ≤
            ∏ j : SpatialScaleIndex i, spatialUnaryIntegralConstant d * (1 + t j) ^ (-(d : ℝ) / 2 - 1) := by
          apply Finset.prod_le_prod₀
          · intro j _
            apply integral_nonneg
            intro y
            have htj : (0 : ℝ) ≤ t j := ht.1 j
            unfold spatialUnaryWeight
            positivity
          · intro j _
            have ht : 0 ≤ (t j) := ht.1 j
            have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
            have hlam : 0 < spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
            have h_spatial_unary_patch_integral_bound : (∫ y in spatialPatchBox d, spatialUnaryWeight (spatialInterpolationLambda d) (t j) x y) ≤
                (8 * Real.exp (1 / 2) / (1 + t j)) *
                  (Real.sqrt (Real.pi / (spatialInterpolationLambda d * (1 + t j) / 2))) ^ d := by
              let lam := spatialInterpolationLambda d
              let b := lam * (1 + t j) / 2
              let A := 8 * Real.exp (1 / 2) / (1 + t j)
              have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
              have hlam : 0 < lam := by dsimp [lam, spatialInterpolationLambda]; positivity
              have hb : 0 < b := by dsimp [b]; positivity
              have hA : 0 ≤ A := by dsimp [A]; positivity
              have hInt := (radial_gaussian_integrable b hb x).const_mul A
              have hbound (y : Covariate d) (hy : y ∈ spatialPatchBox d) :
                  spatialUnaryWeight lam (t j) x y ≤ A * Real.exp (-b * spatialSquaredDistance x y) := by
                obtain ⟨ha, haHalf⟩ := spatial_patch_alpha_bounds hd x y hx hy
                have h := unary_scale_density_gaussian_domination (lam * spatialSquaredDistance x y) (t j) ha haHalf ht
                have he : spatialUnaryWeight lam (t j) x y = unaryScaleDensity (lam * spatialSquaredDistance x y) (t j) := by
                  unfold spatialUnaryWeight unaryScaleDensity
                  congr 2; ring
                rw [← he, show -((1 + (t j)) * (lam * spatialSquaredDistance x y) / 2) =
                  -b * spatialSquaredDistance x y by dsimp [b]; ring] at h
                exact h
              calc
                _ ≤ ∫ y in spatialPatchBox d, A * Real.exp (-b * spatialSquaredDistance x y) :=
                  setIntegral_mono_on (by apply ContinuousOn.integrableOn_compact isCompact_Icc; unfold spatialUnaryWeight spatialSquaredDistance; fun_prop) hInt.integrableOn
                    measurableSet_Icc hbound
                _ ≤ ∫ y, A * Real.exp (-b * spatialSquaredDistance x y) :=
                  integral_mono_measure Measure.restrict_le_self (ae_of_all _ (fun y => by positivity)) hInt
                _ = _ := by rw [integral_const_mul, radial_gaussian_integral]
            apply h_spatial_unary_patch_integral_bound.trans_eq
            rw [radial_gaussian_scale_normalization d _ _ hlam ht]
            unfold spatialUnaryIntegralConstant
            rw [Real.rpow_sub (by linarith), Real.rpow_one]
            ring
        simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] using h
      have hneg : -(d : ℝ) / 2 = -((d : ℝ) / 2) := by ring
      rw [hneg] at hdom
      have h := integral_mono_ae hjoint.integral_prod_left hpowint hdom
      rw [integral_const_mul, spatial_scale_index_card] at h
      have htail := spatial_scale_complement_power_integral_le hn i
        (by linarith : (1 / 2 : ℝ) ≤ (d : ℝ) / 2) hT
      have hh := mul_le_mul_of_nonneg_left htail
        (by unfold spatialUnaryIntegralConstant; positivity :
          0 ≤ (spatialUnaryIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i))
      have he : -2 * (↑d / 2) = -(d : ℝ) := by ring
      rw [spatial_scale_index_card, he] at hh
      calc
        _ ≤ _ := h
        _ ≤ _ := by simpa only [mul_pow, mul_assoc, mul_comm, mul_left_comm] using hh
    calc
      _ ≤ ∫ Y, anchoredCardinalDefect i (spatialInterpolationLambda d) T x Y ∂spatialPatchDesignMeasure i d :=
        integral_mono_ae (anchored_cardinal_defect_square_integrable hd i hlam T x)
          (anchored_cardinal_defect_integrable hd i hlam T x) (Filter.Eventually.of_forall fun Y => by
            have hr := anchored_cardinal_defect_mem_unit i hlam.le T x Y
            nlinarith [hr.1, hr.2])
      _ = ∫ Y, (∫ t : SpatialScaleVector i in Ici 0 \ spatialScaleDomain i T,
            anchoredCardinalScaleWeight i (spatialInterpolationLambda d) x t Y) ∂spatialPatchDesignMeasure i d :=
        integral_congr_ae (anchored_cardinal_defect_ae_eq_tail hd i hlam T x)
      _ ≤ _ := h_anchored_cardinal_tail_spatial_integral_bound
  apply (integral_mono_ae hj.integral_prod_left (integrable_const _) hb).trans_eq
  simp only [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
  change volume.real (spatialPatchBox d) * cardinalDefectSquareBudget d n T = _
  rw [spatialPatchBox_real_volume]
theorem cardinalWeightDefect_sum_square_integral_le  (hd : 0 < d)
    (hn : 2 ≤ n)  (hT : 1 ≤ T) :
    (∫ U, (∑ i : Fin n, cardinalWeightDefect i (spatialInterpolationLambda d) T U) ^ 2
      ∂fullSpatialPatchDesign d n) ≤
      n ^ 2 * 2 ^ d * cardinalDefectSquareBudget d n T := by
  have h := finite_sum_square_integral_le (fullSpatialPatchDesign d n) Finset.univ
    (fun i => cardinalWeightDefect i (spatialInterpolationLambda d) T)
    (↑2 ^ d * cardinalDefectSquareBudget d n T)
    (fun i _ => cardinalWeightDefect_measurable i _ hT)
    (fun i _ => cardinalWeightDefect_square_integrable i
      (by unfold spatialInterpolationLambda; positivity) hT)
    (fun i _ => cardinalWeightDefect_full_square_integral_le hd hn i hT)
  simpa only [Finset.card_univ, Fintype.card_fin, ← mul_assoc] using h
def highCardinalRawNumerator  (ad bd lam T : ℝ) (m D q : ℕ)
    (C a V η : ℝ) (U : Fin n → Covariate d) (p g w : Fin n → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) : ℝ :=
  (∫ᵛ e, highPacketObservable ad bd m n D q C c
    (fun ζ z eps => ∏ i, highCardinalDensityReset ad bd lam U p ζ z eps i)
    (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) e
    ∂<•highPacketSignedMeasure (cardinalSeparatedMeasure d n T) ad bd m n D q C
      (cardinalSeparatedAmplitude lam)) -
    η^2 * (∏ i, p i) * ∑ i, (w i)^2 *
      highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i
theorem highCardinalRawNumerator_eq_alias_defect 
    (ad bd lam ) (haD : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
     (hT : 1 ≤ T) (m D q ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hnD : n ≤ D) (hnF : n ≤ F) (C a V η ) (hC : C ≠ 0)
    (U ) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) :
    highCardinalRawNumerator ad bd lam T m D q C a V η U p g w c y =
      η^2 * (∏ i, p i) * ∑ i, (w i)^2 * (integratedCardinalWeight lam T U i-1) *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i +
      (∏ i, p i) * highResponseDefect q C a V η (integratedCardinalMatrix lam T U)
        g w (fun i => highFrameFeature (U i)) c y := by
  letI := cardinal_separated_measure_finite d n hT
  have hm z (eps : Fin n → ℝ) (i : Fin n) :
      Measurable (fun ζ => highCardinalDensityReset ad bd lam U p ζ z eps i) := by
    exact (Finset.measurable_fun_sum _ (fun l _ =>
      (cardinal_separated_factor_measurable lam l (U i)).const_mul (eps l))).const_mul _ |>.const_add z
  have hb (ζ : CardinalSeparatedMark d n) (e : HighDensityMarkIndex m n D) (i : Fin n) :
      |highCardinalDensityReset ad bd lam U p ζ (densityPacketAtom ad bd m n D e).1
        (densityPacketAtom ad bd m n D e).2 i| ≤ bd := by
    have he := densityPacketAtom_mem ad bd hab.le m n D e
    have h := localDensityReset_mem_interval ad bd haD hab n hn _ he.1 _ he.2 p
      (fun i l => cardinalSeparatedFactor lam ζ l (U i)) i (hp i)
      (fun l => cardinal_separated_factor_abs_le_one lam ζ l (U i) (hU i))
    change |localDensityReset ad bd n _ _ p _ i| ≤ _
    rw [abs_of_nonneg (haD.le.trans h.1)]
    exact h.2
  unfold highCardinalRawNumerator
  rw [highPacketSignedMeasure_factor_integral _ ad bd m n D q C _
    (cardinal_separated_amplitude_measurable lam) (cardinal_separated_cost_integrable lam hT) c _
    (fun z eps => Finset.measurable_fun_prod _ (fun i _ => hm z eps i))
    (bd^n) (pow_nonneg (haD.trans hab).le n)
    (fun ζ e => finite_density_product_abs_bound _ bd (haD.trans hab).le (hb ζ e))
    _ (finePairResponseAtomBound q C c _) (finePairResponseAtomBound_le q C c _)]
  have h_high_cardinal_packet_action_exact (Φ : (HighFrameIndex d F → ℝ) → ℝ) : highSeparatedPacketAction (cardinalSeparatedMeasure d n T) ad bd m n D q C
      (cardinalSeparatedAmplitude lam) c
      (fun ζ z ε => ∏ i, highCardinalDensityReset ad bd lam U p ζ z ε i) Φ =
        (∏ i, p i) * responseMatrixAction q C (integratedCardinalMatrix lam T U) c Φ := by
    have h := highSeparatedPacketAction_count_selector (cardinalSeparatedMeasure d n T) ad bd haD hab
      m n D q hn (hn.trans hnD) (Finset.univ : Finset (Fin n)) (by simpa using hnD)
      (by simpa using hnm) (by simp) p
      (fun ζ i l => cardinalSeparatedFactor lam ζ l (U i))
      (fun i l => cardinal_separated_factor_measurable lam l (U i))
      (fun ζ i l => cardinal_separated_factor_abs_le_one lam ζ l (U i) (hU i)) C
      (cardinalSeparatedAmplitude lam) (cardinal_separated_amplitude_measurable lam)
      (cardinal_separated_cost_integrable lam hT) c Φ
    simp only [highCardinalDensityReset] at ⊢
    rw [h]
    have h_cardinalSeparatedSubsetMatrix_univ : separatedSubsetMatrix (cardinalSeparatedMeasure d n T) n
        (fun ζ i l => cardinalSeparatedFactor lam ζ l (U i))
        (cardinalSeparatedAmplitude (D := F) lam) Finset.univ =
          integratedCardinalMatrix lam T U := by
      funext β β'
      have h_cardinal_density_separated_sym_eq (z : CardinalSeparatedMark d n) (U : Fin n → Covariate d) : densitySeparatedSym n (fun i l => cardinalSeparatedFactor lam z l (U i)) Finset.univ =
        cardinalSeparatedSymmetricFactor lam z U := by
        let e : Fin n ≃ (Finset.univ : Finset (Fin n)) :=
          (Equiv.subtypeUnivEquiv (fun i => Finset.mem_univ i)).symm
        rw [densitySeparatedSym_eq_permutation_average n _ Finset.univ e]
        congr 1
        apply Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n)))
        intro τ
        simpa only [e, Equiv.subtypeUnivEquiv_symm_apply, Equiv.symm_apply_apply,
          Equiv.inv_apply, Equiv.Perm.inv_def] using (Equiv.prod_comp τ (fun l => cardinalSeparatedFactor lam z l (U (τ.symm l))))
      unfold separatedSubsetMatrix
      simp_rw [h_cardinal_density_separated_sym_eq]
      exact (integrated_cardinal_symmetric_separated_exact lam hlam hT U hU β β').symm
    simp only [Finset.card_univ, Fintype.card_fin, ite_true, by simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n)),
      Finset.sum_singleton, h_cardinalSeparatedSubsetMatrix_univ]
  rw [h_high_cardinal_packet_action_exact,
    integrated_cardinal_response_heat hnF q C a V η lam T hC hT U g w c y]
  simp only [mul_sub, sub_mul, mul_one, Finset.sum_sub_distrib]
  ring
theorem high_cardinal_alias_abs_bound  (lam T a V η bd )
    (hlam : 0 ≤ lam) (ha : 0 < a) (hbd : 0 ≤ bd)
    (U : Fin n → Covariate d) (p g w : Fin n → ℝ)
    (hp : ∀ i, |p i| ≤ bd) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ)
    (hMass : ∀ i u, 0 ≤ ternaryMass a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c i) V u)
    (y : Fin n → Fin 3) :
    |η^2 * (∏ i, p i) * ∑ i, (w i)^2 * (integratedCardinalWeight lam T U i-1) *
      highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i| ≤
      (η^2 * bd^n / a^2) * ∑ i, cardinalWeightDefect i lam T U := by
  have hterm (i : Fin n) :
      |(w i)^2 * (integratedCardinalWeight lam T U i-1) *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i| ≤
      cardinalWeightDefect i lam T U * (1/a^2) := by
    have hd := cardinalWeightDefect_mem_unit i hlam T U
    have hw2 : (w i)^2 ≤ 1 := by simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr (hw i)
    have hv := high_response_variance_term_abs_bound a V η ha g w (fun i => highFrameFeature (U i)) c hMass y i
    rw [abs_mul, abs_mul, abs_sq, abs_sub_comm]
    change (w i)^2 * |cardinalWeightDefect i lam T U| *
      |highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i| ≤ _
    rw [abs_of_nonneg hd.1]
    exact (mul_le_mul (mul_le_mul_of_nonneg_right hw2 hd.1) hv (abs_nonneg _)
      (by simpa only [one_mul] using hd.1)).trans_eq (by ring)
  rw [abs_mul, abs_mul, abs_sq]
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left (finite_density_product_abs_bound p bd hbd hp)
    (sq_nonneg η)) ((Finset.abs_sum_le_sum_abs _ Finset.univ).trans (Finset.sum_le_sum (fun i _ => hterm i))) (abs_nonneg _) (mul_nonneg (sq_nonneg η) (pow_nonneg hbd n))
  exact hh.trans_eq (by rw [← Finset.sum_mul]; ring)
def cardinalRawAliasCoefficient (n : ℕ) (bd a η : ℝ) : ℝ := η^2 * bd^n / a^2
def cardinalRawTaylorCoefficient (n q : ℕ) (bd C a ρ η : ℝ) : ℝ :=
  bd^n * highResponseRemainderConstant q C a ρ * n^(2*q+2) * η^(2*q+2)
theorem highCardinalRawNumerator_abs_bound_of_chart 
    (ad bd lam ) (haD : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
     (hT : 1 ≤ T) (m D q ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hnD : n ≤ D) (hnF : n ≤ F) (hq : 1 ≤ q)
    (C a V η ρ ) (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (U ) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hpD : ∀ i, p i ∈ Icc ad bd)
    (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) (y : Fin n → Fin 3) :
    |highCardinalRawNumerator ad bd lam T m D q C a V η U p g w c y| ≤
      cardinalRawAliasCoefficient n bd a η * (∑ i, cardinalWeightDefect i lam T U) +
        cardinalRawTaylorCoefficient n q bd C a ρ η * spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U) := by
  have hCpos := lt_of_lt_of_le zero_lt_one hC
  have hpabs (i : Fin n) : |p i| ≤ bd := by
    rw [abs_of_pos (haD.trans_le (hpD i).1)]
    exact (hpD i).2
  have hMass (i : Fin n) (u : Fin 3) :
      0 ≤ ternaryMass a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c i) V u :=
    hp _ (highFrameCoefficientRegression_abs_le C η ρ hC hη hηρ U hU g w hg hw c hc i) u
  have hAlias := high_cardinal_alias_abs_bound lam T a V η bd hlam ha (haD.trans hab).le
    U p g w hpabs hw c hMass y
  have hRem := high_response_defect_abs_bound q hq C a V η ρ hCpos ha hη hρ hηρ
    (integratedCardinalMatrix lam T U) g w (fun i => highFrameFeature (U i)) c y hc hg hw
    (fun v hv i => highFrameProfile_abs_le_one C hC (U i) (hU i) v hv) hp
  have hTaylor : |(∏ i, p i) * highResponseDefect q C a V η (integratedCardinalMatrix lam T U)
      g w (fun i => highFrameFeature (U i)) c y| ≤
      cardinalRawTaylorCoefficient n q bd C a ρ η * spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U) := by
    rw [abs_mul]
    have hh := mul_le_mul (finite_density_product_abs_bound p bd (haD.trans hab).le hpabs) hRem
      (abs_nonneg _) (pow_nonneg (haD.trans hab).le n)
    exact hh.trans_eq (by unfold cardinalRawTaylorCoefficient spatialMatrixL1; ring)
  rw [highCardinalRawNumerator_eq_alias_defect ad bd lam haD hab hlam hT m D q hn hnm hnD hnF
    C a V η hCpos.ne' U hU p g w hpD c y]
  exact (abs_add_le _ _).trans (add_le_add hAlias hTaylor)
theorem highCardinalRawNumerator_square_bound_of_chart 
    (ad bd lam ) (haD : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
     (hT : 1 ≤ T) (m D q ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hnD : n ≤ D) (hnF : n ≤ F) (hq : 1 ≤ q)
    (C a V η ρ ) (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (U ) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w ) (hpD : ∀ i, p i ∈ Icc ad bd)
    (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) (y : Fin n → Fin 3) :
    highCardinalRawNumerator ad bd lam T m D q C a V η U p g w c y ^ 2 ≤
      2 * cardinalRawAliasCoefficient n bd a η ^ 2 * (∑ i, cardinalWeightDefect i lam T U)^2 +
      2 * cardinalRawTaylorCoefficient n q bd C a ρ η ^ 2 *
        spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U)^2 := by
  have h := highCardinalRawNumerator_abs_bound_of_chart ad bd lam haD hab hlam hT m D q
    hn hnm hnD hnF hq C a V η ρ hC ha hη hρ hηρ U hU p g w hpD hg hw c hc hp y
  have hsum : 0 ≤ ∑ i, cardinalWeightDefect i lam T U :=
    Finset.sum_nonneg (fun i _ => (cardinalWeightDefect_mem_unit i hlam T U).1)
  have : 0 ≤ bd := (haD.trans hab).le
  have hB : 0 ≤ cardinalRawTaylorCoefficient n q bd C a ρ η := by
    unfold cardinalRawTaylorCoefficient highResponseRemainderConstant
    have : 0 ≤ highResponseDerivativeBudget a ρ :=
      zero_le_one.trans (highResponseDerivativeBudget_guards a ρ).1
    positivity
  have hh := (sq_le_sq₀ (abs_nonneg _) (add_nonneg (mul_nonneg (by unfold cardinalRawAliasCoefficient; positivity) hsum) (mul_nonneg hB (by unfold spatialMatrixL1; exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)))))).mpr h
  rw [sq_abs] at hh
  nlinarith only [hh, sq_nonneg (cardinalRawAliasCoefficient n bd a η * (∑ i, cardinalWeightDefect i lam T U) -
    cardinalRawTaylorCoefficient n q bd C a ρ η * spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U))]
def cardinalRawSpatialEnergyBudget (d n q : ℕ) (bd C a ρ η T : ℝ) : ℝ :=
  2 * cardinalRawAliasCoefficient n bd a η ^ 2 *
      n^2 * 2^d * cardinalDefectSquareBudget d n T +
    2 * cardinalRawTaylorCoefficient n q bd C a ρ η ^ 2 *
      (n^2 * 2^d *
        ((100*d)^2*16*spatialScaleIntegralConstant d)^(n-1))
end
variable {d R r n F : ℕ} {c0 K N ad bd : ℝ}
def cardinalBandDimensionConstant (d : ℕ) : ℝ :=
  (100 * (d : ℝ))^2 * 16 * spatialScaleIntegralConstant d
theorem cardinalBandDimensionConstant_nonneg (d : ℕ) :
    0 ≤ cardinalBandDimensionConstant d := by
  unfold cardinalBandDimensionConstant spatialScaleIntegralConstant
  positivity
def lowerAliasSpatialA (d R : ℕ) : ℝ :=
  (R : ℝ)^2 * (2 : ℝ)^d * (1+cardinalBandDimensionConstant d)^R
def lowerAliasSpatialL (d : ℕ) (R : ℕ) (c0 K : ℝ) : ℝ :=
  c0*K*((d : ℝ)-4) + R
theorem lowerAliasSpatialL_nonneg  (hd : 4 ≤ d) 
    (hc0 : 0 ≤ c0) (_hK : 0 ≤ K) : 0 ≤ lowerAliasSpatialL d R c0 K := by
  unfold lowerAliasSpatialL
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  positivity
theorem cardinalBandSquareBudget_cutoff_le  {M D K c0 N : ℝ}
    (hd : 4 ≤ d) (hr : r ≤ R) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hK : 0 ≤ K) (hc0 : 0 ≤ c0) (hDK : D ≤ K*M) (hN : 0 < N)
    (hell : 1 ≤ N*Real.exp (-c0*D))
    (hH : Real.log (1+Real.log N) ≤ M) :
    (r : ℝ)^2 * (2 : ℝ)^d * cardinalBandSquareBudget d r (N*Real.exp (-c0*D)) ≤
      lowerAliasSpatialA d R * N^(4-(d : ℝ)) * Real.exp (lowerAliasSpatialL d R c0 K * M) := by
  have hC := cardinalBandDimensionConstant_nonneg d
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have he1 : Real.exp (-c0*D) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hellN : N*Real.exp (-c0*D) ≤ N := by nlinarith
  have hN1 : 1 ≤ N := hell.trans hellN
  have hHp : 0 < 1+Real.log N := by linarith [Real.log_nonneg hN1]
  have hlog : 1+Real.log (N*Real.exp (-c0*D)) ≤ 1+Real.log N :=
    add_le_add_right (Real.log_le_log (by positivity) hellN) 1
  have hlog0 : 0 ≤ 1+Real.log (N*Real.exp (-c0*D)) := by linarith [Real.log_nonneg hell]
  have hHexp : 1+Real.log N ≤ Real.exp M := by
    simpa only [Real.exp_log hHp] using Real.exp_le_exp.mpr hH
  have hexp1 : 1 ≤ Real.exp M := Real.one_le_exp_iff.mpr hM
  have hlogpower : (1+Real.log (N*Real.exp (-c0*D)))^(r-2) ≤ Real.exp ((R : ℝ)*M) := by
    calc
      _ ≤ (Real.exp M)^(r-2) := pow_le_pow_left₀ hlog0 (hlog.trans hHexp) _
      _ ≤ (Real.exp M)^R := pow_le_pow_right₀ hexp1 (by omega)
      _ = _ := (Real.exp_nat_mul M R).symm
  have hCpower : (cardinalBandDimensionConstant d)^(r-1) ≤ (1+cardinalBandDimensionConstant d)^R := by
    exact (pow_le_pow_left₀ hC (by linarith) (r-1)).trans
      (pow_le_pow_right₀ (by linarith) (by omega))
  have hr2 : (r : ℝ)^2 ≤ (R : ℝ)^2 := by exact_mod_cast Nat.pow_le_pow_left hr 2
  have hscale : (N*Real.exp (-c0*D))^(4-(d : ℝ)) ≤
      N^(4-(d : ℝ)) * Real.exp ((c0*K*((d : ℝ)-4))*M) := by
    rw [Real.mul_rpow hN.le (Real.exp_pos _).le, ← Real.exp_mul]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hN.le _)
    apply Real.exp_le_exp.mpr
    have hp := mul_le_mul_of_nonneg_left hDK (show 0 ≤ c0*((d : ℝ)-4) by positivity)
    nlinarith
  have hbound := mul_le_mul (mul_le_mul (mul_le_mul hr2 (le_refl ((2 : ℝ)^d)) (by positivity) (sq_nonneg _))
      hCpower (by positivity) (by positivity))
    (mul_le_mul hscale hlogpower (by positivity) (by positivity)) (by positivity) (by positivity)
  unfold cardinalBandSquareBudget cardinalBandDimensionConstant at hbound
  calc
    _ = (r : ℝ)^2 * (2 : ℝ)^d * (cardinalBandDimensionConstant d)^(r-1) *
        ((N*Real.exp (-c0*D))^(4-(d : ℝ)) * (1+Real.log (N*Real.exp (-c0*D)))^(r-2)) := by
      unfold cardinalBandSquareBudget cardinalBandDimensionConstant
      ring
    _ ≤ _ := hbound
    _ = _ := by
      unfold lowerAliasSpatialA lowerAliasSpatialL cardinalBandDimensionConstant
      rw [show Real.exp ((c0*K*((d : ℝ)-4)+(R : ℝ))*M) =
        Real.exp ((c0*K*((d : ℝ)-4))*M) * Real.exp ((R : ℝ)*M) by rw [← Real.exp_add]; congr 1; ring]
      ring
def lowerAliasSpatialFixedL (d : ℕ) (θ c0 : ℝ) : ℝ :=
  lowerAliasSpatialL d (lowerAliasFineTargetBound d θ c0) c0 (((d : ℝ)+8)/4+1)
def ordinaryFineAliasRawAction  (ad bd lam L T : ℝ) (M r q : ℕ)
    (C a V η : ℝ) (U : Fin n → Covariate d) (p g w : Fin n → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) : ℝ :=
  densityCountCoefficient ad bd M r n *
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
      (∏ i ∈ S, p i) * responseMatrixAction q C
        (globalCardinalBandMatrix lam L T (spatialSubsetConfiguration S U)) c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)
theorem ordinary_count_product_shrunk_abs_bound {n M r R : ℕ}
    (ad bd c0 : ℝ) (ha : 0 < ad)
    (hshrink : ad+(M : ℝ)⁻¹ < bd-(M : ℝ)⁻¹)
    (htau : shrunkDensityExponent ad bd M ≤ c0) (hr : 1 ≤ r) (hrR : r ≤ R)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹))
    (S : Finset (Fin n)) (hS : S.card = r) :
    |densityCountCoefficient (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹) M r n * (∏ i ∈ S, p i)| ≤
      (1+bd)^n * (1+uniformOrdinaryDensityActivityBase ad bd c0)^R *
        Real.exp ((M : ℝ)*shrunkDensityExponent ad bd M) := by
  have ht : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hab : ad < bd := by linarith
  have hap : 0 < ad+(M : ℝ)⁻¹ := by linarith
  have he : exteriorTau (((ad+(M : ℝ)⁻¹)+(bd-(M : ℝ)⁻¹))/
      ((bd-(M : ℝ)⁻¹)-(ad+(M : ℝ)⁻¹))) = shrunkDensityExponent ad bd M := by
    rw [exteriorTau_sqrt_ratio _ _ hap hshrink]
    rfl
  have hb := ordinaryDensityActivityBase_shrunk_le ha ht hshrink htau
  have hbn : (bd-(M : ℝ)⁻¹)^n ≤ (1+bd)^n :=
    pow_le_pow_left₀ (hap.trans hshrink).le (by linarith) n
  have hBr : (ordinaryDensityActivityBase (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹))^r ≤
      (1+uniformOrdinaryDensityActivityBase ad bd c0)^R := by
    have hbase : 0 ≤ ordinaryDensityActivityBase (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹) := by
      unfold ordinaryDensityActivityBase
      positivity
    exact (pow_le_pow_left₀ hbase (hb.trans (by linarith)) r).trans
      (pow_le_pow_right₀ (by linarith) hrR)
  have h_ordinary_count_product_abs_bound (ad : ℝ) (bd : ℝ) (ha : 0 < ad) (hab : ad < bd) (hp : ∀ i, p i ∈ Icc ad bd) : |densityCountCoefficient ad bd M r n * (∏ i ∈ S, p i)| ≤
      bd^n * (ordinaryDensityActivityBase ad bd)^r *
        Real.exp ((M : ℝ) * exteriorTau ((ad+bd)/(bd-ad))) := by
    have hbd  := ha.trans hab
    have hm  := abs_pos.mpr (densityMargin_zero_ne ad bd ha hab)
    have hτ : 0 ≤ exteriorTau ((ad+bd)/(bd-ad)) := by
      rw [exteriorTau_sqrt_ratio ad bd ha hab]
      exact (densityIntervalExponent_pos ha hab).le
    have hprod : |∏ i ∈ S, p i| ≤ bd^r := by
      rw [Finset.abs_prod]
      calc
        _ ≤ ∏ i ∈ S, bd := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => by
          simpa only [abs_of_pos (ha.trans_le (hp i).1)] using (hp i).2)
        _ = _ := by rw [Finset.prod_const, hS]
    have h_densityCountCoefficient_abs_bound : |densityCountCoefficient ad bd M r n| ≤
        (bd ^ (n - r) * ((bd - ad) / 4) ^ r / |densityMargin ad bd 0| ^ r) *
          Real.cosh ((M + r : ℕ) * exteriorTau ((ad + bd) / (bd - ad))) := by
      have hb : ∀ j : Fin (M + r + 1),
          |exteriorNode ad bd (M + r) j ^ (n - r) *
            densityMargin ad bd (exteriorNode ad bd (M + r) j) ^ r| ≤
          bd ^ (n - r) * ((bd - ad) / 4) ^ r := by
        intro j
        have hz := exteriorNode_mem ad bd hab.le (M + r) j
        have ht := densityMargin_bounds ad bd hab _ hz
        rw [abs_mul, abs_pow, abs_pow, abs_of_nonneg (ha.le.trans hz.1), abs_of_nonneg ht.1]
        exact mul_le_mul (pow_le_pow_left₀ (ha.le.trans hz.1) hz.2 _)
          (pow_le_pow_left₀ ht.1 ht.2.2.2 _) (pow_nonneg ht.1 _) (pow_nonneg ((ha.trans hab).le) _)
      have hs : |∑ j : Fin (M + r + 1), exteriorWeight ad bd (M + r) j *
          (exteriorNode ad bd (M + r) j ^ (n - r) *
            densityMargin ad bd (exteriorNode ad bd (M + r) j) ^ r)| ≤
          Real.cosh ((M + r : ℕ) * exteriorTau ((ad + bd) / (bd - ad))) *
            (bd ^ (n - r) * ((bd - ad) / 4) ^ r) := by
        calc
          _ ≤ ∑ j : Fin (M + r + 1), |exteriorWeight ad bd (M + r) j| *
              (bd ^ (n - r) * ((bd - ad) / 4) ^ r) := by
            apply (Finset.abs_sum_le_sum_abs _ _).trans
            apply Finset.sum_le_sum
            intro j _
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hb j) (abs_nonneg _)
          _ = _ := by rw [← Finset.sum_mul, exterior_rule_variation ad bd ha hab _ (by omega)]
      unfold densityCountCoefficient
      rw [abs_div, abs_pow]
      exact (div_le_div_of_nonneg_right hs (by positivity)).trans_eq (by ring)
    have hcoeff := h_densityCountCoefficient_abs_bound
    have hcosh : Real.cosh ((M+r : ℕ)*exteriorTau ((ad+bd)/(bd-ad))) ≤
        Real.exp ((M+r : ℕ)*exteriorTau ((ad+bd)/(bd-ad))) := by
      rw [Real.cosh_eq]
      have he := Real.exp_le_exp.mpr (show -((M+r : ℕ)*exteriorTau ((ad+bd)/(bd-ad))) ≤
        ((M+r : ℕ)*exteriorTau ((ad+bd)/(bd-ad))) by
          have hh := mul_nonneg (Nat.cast_nonneg (M+r)) hτ
          linarith)
      linarith
    have hj : (bd-ad)/4 ≤ bd := by linarith
    have he : Real.exp (exteriorTau ((ad+bd)/(bd-ad))) ≤
        Real.exp (1+exteriorTau ((ad+bd)/(bd-ad))) := Real.exp_le_exp.mpr (by linarith)
    have hb : (bd-ad)/4/|densityMargin ad bd 0| * Real.exp (exteriorTau ((ad+bd)/(bd-ad))) ≤
        ordinaryDensityActivityBase ad bd := by
      unfold ordinaryDensityActivityBase
      rw [abs_div, abs_of_pos hbd]
      exact (mul_le_mul (div_le_div_of_nonneg_right hj hm.le) he
        (Real.exp_pos _).le (div_nonneg hbd.le hm.le)).trans_eq (by ring)
    have h1 := mul_le_mul hcoeff hprod (abs_nonneg _) (by positivity)
    have h2 := mul_le_mul_of_nonneg_left hcosh
      (show 0 ≤ (bd^(n-r)*((bd-ad)/4)^r/|densityMargin ad bd 0|^r)*bd^r by positivity)
    have hid : ((bd^(n-r)*((bd-ad)/4)^r/|densityMargin ad bd 0|^r)*bd^r)*
        Real.exp ((M+r : ℕ)*exteriorTau ((ad+bd)/(bd-ad))) =
        bd^n * (((bd-ad)/4/|densityMargin ad bd 0|)*Real.exp (exteriorTau ((ad+bd)/(bd-ad))))^r *
          Real.exp ((M : ℝ)*exteriorTau ((ad+bd)/(bd-ad))) := by
      have heq : Real.exp ((M+r : ℕ)*exteriorTau ((ad+bd)/(bd-ad))) =
          Real.exp ((M : ℝ)*exteriorTau ((ad+bd)/(bd-ad))) *
            (Real.exp (exteriorTau ((ad+bd)/(bd-ad))))^r := by
        rw [Nat.cast_add, add_mul, Real.exp_add]
        congr 1
        simpa only [mul_comm] using Real.exp_nat_mul (exteriorTau ((ad+bd)/(bd-ad))) r
      rw [heq]
      generalize (bd-ad)/4 = J
      generalize |densityMargin ad bd 0| = H
      generalize Real.exp (exteriorTau ((ad+bd)/(bd-ad))) = X
      generalize Real.exp ((M : ℝ)*exteriorTau ((ad+bd)/(bd-ad))) = Y
      rw [mul_pow, div_pow]
      have hpw : bd^(n-r)*bd^r = bd^n := by rw [← pow_add, Nat.sub_add_cancel (by simpa only [hS, Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ S)]
      calc _ = bd^(n-r)*bd^r *
          (J^r/H^r) * X^r * Y := by ring
           _ = _ := by rw [hpw]; ring
    have h3 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb r) (pow_nonneg hbd.le n))
      (Real.exp_pos ((M : ℝ)*exteriorTau ((ad+bd)/(bd-ad)))).le
    calc
      _ ≤ (bd^(n-r)*((bd-ad)/4)^r/|densityMargin ad bd 0|^r)*bd^r *
          Real.cosh ((M+r : ℕ)*exteriorTau ((ad+bd)/(bd-ad))) := by
        simpa only [abs_mul, mul_assoc, mul_left_comm, mul_comm] using h1
      _ ≤ _ := h2
      _ = _ := hid
      _ ≤ _ := h3
  have h := (h_ordinary_count_product_abs_bound (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹) hap hshrink hp)
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hbn hBr
      (pow_nonneg (by unfold ordinaryDensityActivityBase; positivity) r)
      (pow_nonneg (by linarith) n)) (Real.exp_pos _).le)
def ordinaryAliasResponseConstant (q : ℕ) (C a ρ : ℝ) : ℝ :=
  2*C^2 * (∑ j : Fin (2*q+2), |responseWeight q j|) * highSeparatedDerivativeBudget a ρ
theorem ordinaryFineAliasRawAction_abs_bound_of_chart {d n F M r R : ℕ}
    (ad bd c0 lam L T : ℝ) (haD : 0 < ad)
    (hshrink : ad+(M : ℝ)⁻¹ < bd-(M : ℝ)⁻¹)
    (htau : shrunkDensityExponent ad bd M ≤ c0) (hr : 1 ≤ r) (hrR : r ≤ R)
    (q : ℕ) (hn : 1 ≤ n) (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a)
    (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ)
    (hpD : ∀ i, p i ∈ Icc (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹))
    (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) (y : Fin n → Fin 3) :
    |ordinaryFineAliasRawAction (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹) lam L T M r q C a V η U p g w c y| ≤
      ((1+bd)^n * (1+uniformOrdinaryDensityActivityBase ad bd c0)^R *
        Real.exp ((M : ℝ)*shrunkDensityExponent ad bd M)) *
      ordinaryAliasResponseConstant q C a ρ * (n : ℝ)^2 * η^2 *
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
          spatialMatrixL1 (globalCardinalBandMatrix (D := F) lam L T (spatialSubsetConfiguration S U)) := by
  unfold ordinaryFineAliasRawAction
  rw [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hterm (S) (hmem : S ∈ (Finset.univ : Finset (Fin n)).powersetCard r) :=
    ordinary_count_product_shrunk_abs_bound ad bd c0 haD hshrink htau hr hrR p hpD S ((fun S hS => (Finset.mem_powersetCard.mp hS).2) S hmem)
  have hresponse (S : Finset (Fin n)) := high_response_matrix_all_count_bound q hn C a V η ρ
    (lt_of_lt_of_le zero_lt_one hC) ha hη hρ hηρ
    (globalCardinalBandMatrix (D := F) lam L T (spatialSubsetConfiguration S U))
    g w (fun i => highFrameFeature (U i)) c y hc hg hw
    (fun v hv i => highFrameProfile_abs_le_one C hC (U i) (hU i) v hv) hp
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hmem
  have hh := mul_le_mul (hterm S hmem) (hresponse S) (abs_nonneg _)
    (show 0 ≤ (1+bd)^n * (1+uniformOrdinaryDensityActivityBase ad bd c0)^R *
      Real.exp ((M : ℝ)*shrunkDensityExponent ad bd M) by
        have ht : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg M)
        have : 0 < bd := by linarith
        have : ad < bd := by linarith
        unfold uniformOrdinaryDensityActivityBase
        positivity)
  simpa only [abs_mul, mul_assoc] using hh.trans_eq (by
    unfold ordinaryAliasResponseConstant highSeparatedDerivativeBudget spatialMatrixL1
    ring)
theorem ordinaryFineAliasKernel_sum_square_integrable_and_le 
    (hd : 5 ≤ d) (hr : 2 ≤ r) {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T) :
    Integrable (fun U : Fin n → Covariate d =>
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        spatialMatrixL1 (globalCardinalBandMatrix (D := F) (spatialInterpolationLambda d) L T
          (spatialSubsetConfiguration S U)))^2) (fullSpatialPatchDesign d n) ∧
    (∫ U : Fin n → Covariate d,
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        spatialMatrixL1 (globalCardinalBandMatrix (D := F) (spatialInterpolationLambda d) L T
          (spatialSubsetConfiguration S U)))^2 ∂fullSpatialPatchDesign d n) ≤
      (n.choose r : ℝ)^2 * (2 : ℝ)^(d*(n-r)) *
        ((r : ℝ)^2*(2 : ℝ)^d*cardinalBandSquareBudget d r L) := by
  let f := fun (S : Finset (Fin n)) (V : Fin S.card → Covariate d) =>
    spatialMatrixL1 (globalCardinalBandMatrix (D := F) (spatialInterpolationLambda d) L T V)
  have hf (S : Finset (Fin n)) : Measurable (f S) := by
    exact Finset.measurable_sum _ (fun γ _ => Finset.measurable_sum _
      (fun δ _ => (integrated_cardinal_band_continuous (spatialInterpolationLambda d) hL hT γ δ).measurable.abs))
  have hs (S) (hS : S ∈ (Finset.univ : Finset (Fin n)).powersetCard r) : S.card = r :=
    (Finset.mem_powersetCard.mp hS).2
  have hi (S) (hS : S ∈ (Finset.univ : Finset (Fin n)).powersetCard r) :
      Integrable (fun V => f S V^2) (fullSpatialPatchDesign d S.card) :=
    globalCardinalBandMatrix_square_integrable hd (by rw [hs S hS]; exact hr) hL hT hLT
  constructor
  · have h := finite_sum_abs_square_integrable (fullSpatialPatchDesign d n)
      ((Finset.univ : Finset (Fin n)).powersetCard r)
      (fun S U => f S (spatialSubsetConfiguration S U))
      (fun S _ => (hf S).comp (spatialSubsetConfiguration_measurable S))
      (fun S hS => spatial_subset_square_integrable_enumerated S (f S) (hi S hS))
    simpa only [f, abs_of_nonneg (spatial_matrix_l1_nonnegative _)] using h
  · exact spatial_subset_sum_square_integral_le f _ (fun S _ => hf S) hi
      (fun S hS => by
        have h := globalCardinalBandMatrix_square_integral_le (D := F) hd
          (show 2 ≤ S.card by rw [hs S hS]; exact hr) hL hT hLT
        simpa only [f, hs S hS] using h)
def ordinaryFineAliasSpatialBudget (d n M r R q : ℕ) (ad bd c0 C a ρ η L : ℝ) : ℝ :=
  (((1+bd)^n * (1+uniformOrdinaryDensityActivityBase ad bd c0)^R *
      Real.exp ((M : ℝ)*shrunkDensityExponent ad bd M)) *
    ordinaryAliasResponseConstant q C a ρ * (n : ℝ)^2 * η^2)^2 *
      ((n.choose r : ℝ)^2 * (2 : ℝ)^(d*(n-r)) *
        (r : ℝ)^2*(2 : ℝ)^d*cardinalBandSquareBudget d r L)
def ordinaryAliasSpatialPrefactor (d q R : ℕ) (ad bd c0 C a ρ : ℝ) : ℝ :=
  ((1+uniformOrdinaryDensityActivityBase ad bd c0)^R)^2 *
    (ordinaryAliasResponseConstant q C a ρ)^2 * lowerAliasSpatialA d R
def ordinaryAliasSpatialCountBase (d : ℕ) (bd : ℝ) : ℝ :=
  64*(2 : ℝ)^d*(1+bd)^2
def ordinaryAliasSpatialResponseBase (d : ℕ) (bd : ℝ) : ℝ :=
  3*ordinaryAliasSpatialCountBase d bd
theorem ordinaryAliasSpatialPrefactor_nonneg (d q R : ℕ) (ad bd c0 C a ρ : ℝ) :
    0 ≤ ordinaryAliasSpatialPrefactor d q R ad bd c0 C a ρ := by
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by unfold lowerAliasSpatialA; have := cardinalBandDimensionConstant_nonneg d; positivity)
theorem ordinaryFineAliasSpatialBudget_source_scale_le {d n M r R : ℕ}
    (hd : 5 ≤ d) (hrR : r ≤ R) {ad bd c0 C a ρ η D K N : ℝ}
    (hbd : 0 ≤ bd) (hD : 0 ≤ D) (hK : 0 ≤ K) (hc0 : 0 ≤ c0)
    (hDK : D ≤ K*M) (hN : 0 < N) (hell : 1 ≤ N*Real.exp (-c0*D))
    (hH : Real.log (1+Real.log N) ≤ M) (q : ℕ) :
    ordinaryFineAliasSpatialBudget d n M r R q ad bd c0 C a ρ η (N*Real.exp (-c0*D)) ≤
      ordinaryAliasSpatialPrefactor d q R ad bd c0 C a ρ *
        η^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ)) *
          Real.exp (lowerAliasSpatialL d R c0 K*M) * (ordinaryAliasSpatialCountBase d bd)^n := by
  have hkernel := cardinalBandSquareBudget_cutoff_le (by omega : 4 ≤ d) hrR
    (Nat.cast_nonneg M) hD hK hc0 hDK hN hell hH
  have h_ordinary_alias_count_factors_le : ((1+bd)^n)^2 * (n : ℝ)^4 * (n.choose r : ℝ)^2 * (2 : ℝ)^(d*(n-r)) ≤
      (64*(2 : ℝ)^d*(1+bd)^2)^n := by
    have hn : (n : ℝ) ≤ (2 : ℝ)^n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
    have hc : (n.choose r : ℝ) ≤ (2 : ℝ)^n := by exact_mod_cast Nat.choose_le_two_pow n r
    have hn4 : (n : ℝ)^4 ≤ (16 : ℝ)^n := by
      have h := pow_le_pow_left₀ (Nat.cast_nonneg n) hn 4
      convert h using 1 <;> rw [← pow_mul, Nat.mul_comm n 4, pow_mul] <;> norm_num
    have hc2 : (n.choose r : ℝ)^2 ≤ (4 : ℝ)^n := by
      have h := pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
      convert h using 1 <;> rw [← pow_mul, Nat.mul_comm n 2, pow_mul] <;> norm_num
    have hv : (2 : ℝ)^(d*(n-r)) ≤ ((2 : ℝ)^d)^n := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left d (Nat.sub_le n r))
    have h := mul_le_mul (mul_le_mul (mul_le_mul (le_refl (((1+bd)^n)^2)) hn4
        (by positivity) (by positivity)) hc2 (by positivity) (by positivity)) hv (by positivity) (by positivity)
    apply h.trans_eq
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, ← mul_pow, ← mul_pow, ← mul_pow]
    congr 1
    ring
  have hcount := h_ordinary_alias_count_factors_le
  let P := ((1+uniformOrdinaryDensityActivityBase ad bd c0)^R)^2 *
    (ordinaryAliasResponseConstant q C a ρ)^2 * η^4 * Real.exp (2*shrunkDensityExponent ad bd M*M)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have he : (Real.exp ((M : ℝ)*shrunkDensityExponent ad bd M))^2 =
      Real.exp (2*shrunkDensityExponent ad bd M*M) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hid : ordinaryFineAliasSpatialBudget d n M r R q ad bd c0 C a ρ η (N*Real.exp (-c0*D)) =
      P * (((1+bd)^n)^2 * (n : ℝ)^4 * (n.choose r : ℝ)^2 * (2 : ℝ)^(d*(n-r))) *
        ((r : ℝ)^2*(2 : ℝ)^d*cardinalBandSquareBudget d r (N*Real.exp (-c0*D))) := by
    unfold ordinaryFineAliasSpatialBudget P
    rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, he]
    ring
  rw [hid]
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hcount hP) hkernel (by
      unfold cardinalBandSquareBudget
      have := cardinalBandDimensionConstant_nonneg d
      have hlog : 0 ≤ 1+Real.log (N*Real.exp (-c0*D)) := by linarith [Real.log_nonneg hell]
      positivity) (by positivity)
  exact hh.trans_eq (by unfold P ordinaryAliasSpatialPrefactor ordinaryAliasSpatialCountBase; ring)
def ordinaryFineAliasTargetSet (d D : ℕ) (L N mu : ℝ) : Finset ℕ :=
  (Finset.range (D+1)).filter (fun r => 3 ≤ r ∧ L < higherBandTargetScale d r N mu)
def ordinaryFineAliasFamilyRawAction  (I : Finset ℕ)
    (ad bd lam L : ℝ) (T : ℕ → ℝ) (M q : ℕ) (C a V eta : ℝ)
    (U : Fin n → Covariate d) (p g w : Fin n → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) : ℝ :=
  ∑ r ∈ I, ordinaryFineAliasRawAction ad bd lam L (T r) M r q C a V eta U p g w c y
def ordinaryAliasFamilySpatialPrefactor (d q R : ℕ) (ad bd c0 C a rho : ℝ) : ℝ :=
  ((R+1 ) : ℝ)^2 * ordinaryAliasSpatialPrefactor d q R ad bd c0 C a rho
theorem ordinaryAliasFamilySpatialPrefactor_nonneg (d q R ad bd c0 C a rho) :
    0 ≤ ordinaryAliasFamilySpatialPrefactor d q R ad bd c0 C a rho :=
  mul_nonneg (sq_nonneg _) (ordinaryAliasSpatialPrefactor_nonneg _ _ _ _ _ _ _ _ _)
structure OrdinaryFineAliasSaddleGuards (s : ℝ) (d : ℕ) (ad bd Cw x : ℝ) : Prop where
  dimension : 5 ≤ d
  degree : (lowerSaddleD d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x : ℝ) ≤
    (((d : ℝ)+8)/4+1)*(lowerSaddleM (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x : ℝ)
  cutoff : 1 ≤ lowerAliasCutoff s d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
    (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw (densityIntervalExponent ad bd+1)
    (shrunkDensityExponent ad bd) x
  logarithm : Real.log (1+Real.log (lowerSaddleN s d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
    (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw (shrunkDensityExponent ad bd) x)) ≤
      lowerSaddleM (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x
  targets : ∀ r ∈ ordinaryFineAliasTargetSet d
    (lowerSaddleD d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x)
    (lowerAliasCutoff s d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
      (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw (densityIntervalExponent ad bd+1)
      (shrunkDensityExponent ad bd) x)
    (lowerSaddleN s d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
      (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw (shrunkDensityExponent ad bd) x)
    (lowerSaddleMu d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
      (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw x),
    2 ≤ r ∧ r ≤ lowerAliasFineTargetBound d
      (lowerSaddleTheta s d (densityIntervalExponent ad bd)) (densityIntervalExponent ad bd+1)
theorem eventually_ordinaryFineAlias_saddle_guards {s ad bd : ℝ} 
    (hs : 1 < s) (hd : 4*s < (d : ℝ)) (haD : 0 < ad) (hab : ad < bd) (Cw : ℝ) :
    ∀ᶠ x in atTop, OrdinaryFineAliasSaddleGuards s d ad bd Cw x := by
  let m := lowerSaddleCoefficient s d (densityIntervalExponent ad bd)
  filter_upwards [actual_lowerAlias_hierarchy hs hd haD hab (Cact := 1) (Cs := 1)
      (by norm_num) (by norm_num) Cw,
    (lowerSaddleM_tendsto_atTop (lowerSaddleCoefficient_pos hs hd (densityIntervalExponent_pos haD hab))).eventually (eventually_ge_atTop 1)] with x hh hM1
  rcases hh with ⟨hell,_,_hbase,hlog,_hgap,_hq21,_hq1,_hDq,_hco,_hsingle,_hRM,hactive⟩
  have : (0 : ℝ)<d := by linarith
  have h : (4 : ℝ)<d := by linarith
  have : 4<d := by exact_mod_cast h
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (d+8)/4*(lowerSaddleM m x : ℝ) by positivity)
  refine ⟨by omega,
    (by change (lowerSaddleD d m x : ℝ) < (d+8)/4*(lowerSaddleM m x : ℝ)+1 at hceil; nlinarith), hell.le, hlog, ?_⟩
  intro r hr
  have hrmem := (Finset.mem_filter.mp hr).2
  refine ⟨by omega, hactive r ?_⟩
  exact hrmem.2
theorem higherBand_coarse_below_one_signed_zero (d r m D q ) (a b C lam L T : ℝ)
    (hT : 0 < T) (hT1 : T < 1) : higherBandSignedRow d r m D q a b C lam L T false = 0 := by
  have h_cardinal_separated_measure_below_one_eq_zero : cardinalSeparatedMeasure d r T = 0 := by
    have h_centered_cardinal_measure_below_one_eq_zero {n : ℕ} (i : Fin n) : centeredCardinalMeasure i d T = 0 := by
      simp only [centeredCardinalMeasure, spatialScaleMeasure,
        spatial_scale_domain_empty_below_one i hT hT1, Measure.restrict_empty, Measure.zero_prod]
    unfold cardinalSeparatedMeasure
    simp_rw [h_centered_cardinal_measure_below_one_eq_zero _, Measure.map_zero]
    exact Finset.sum_const_zero
  rw [higherBandSignedRow, higherBandCarrierMeasure,
    h_cardinal_separated_measure_below_one_eq_zero, highPacketSignedMeasure, Measure.zero_prod]
  ext1 s hs
  rw [withDensityᵥ_apply (by simp : Integrable _ (0 : Measure _)) hs]
  simp
def higherBandFamilyRowIntegral (d D M q ) (a b C lam ell N mu : ℝ)
    (F : (i : Fin (D-2) × Bool) →
      HigherBandRowMark d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q i.2 → ℝ)
    (i : Fin (D-2) × Bool) : ℝ :=
  ∫ᵛ e, F i e ∂<•higherBandSignedRow d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q
    a b C lam ell (higherBandFamilyUpper d ell N mu i) i.2
def higherBandPhysicalIntegral (d D M q ) (a b C lam ell N mu : ℝ)
    (F : (i : Fin (D-2) × Bool) →
      HigherBandRowMark d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q i.2 → ℝ)
    (i : Fin (D-2) × Bool) : ℝ :=
  if i.2 = true then
    if ell < higherBandTargetScale d (higherBandFamilyTarget i) N mu then
      higherBandFamilyRowIntegral d D M q a b C lam ell N mu F i else 0
  else higherBandFamilyRowIntegral d D M q a b C lam ell N mu F i
theorem higherBandPhysicalIntegral_selected (d D M q a b C lam ell N mu F i) (hi : HigherBandFamilySelected d D M q a b C lam ell N mu i) :
    higherBandPhysicalIntegral d D M q a b C lam ell N mu F i =
      higherBandFamilyRowIntegral d D M q a b C lam ell N mu F i := by
  unfold higherBandPhysicalIntegral
  by_cases hf : i.2 = true
  · rw [ite_eq_left hf, ite_eq_left (hi.2.1 hf)]
  · rw [ite_eq_right hf]
theorem higherBandPhysicalIntegral_unselected_zero (d D M q a b C lam ell N mu)
    (hell : 1 ≤ ell)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu)
    (hFine : ∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M)
    (F i) (hi : ¬HigherBandFamilySelected d D M q a b C lam ell N mu i) :
    higherBandPhysicalIntegral d D M q a b C lam ell N mu F i = 0 := by
  rcases i with ⟨j, fine⟩
  cases fine
  · simp only [higherBandPhysicalIntegral, Bool.false_eq_true, ite_false]
    by_cases hT1 : 1 ≤ min ell (higherBandTargetScale d (j.val+3) N mu)
    · have hz : higherBandRowMass d (j.val+3) D D q a b C lam ell
          (min ell (higherBandTargetScale d (j.val+3) N mu)) false = 0 := by
        have hn := higherBandRowMass_nonneg d (j.val+3) D D q a b C lam ell
          (min ell (higherBandTargetScale d (j.val+3) N mu)) false
        apply le_antisymm _ hn
        apply le_of_not_gt
        intro hp
        apply hi
        change (1 ≤ min ell (higherBandTargetScale d (j.val+3) N mu)) ∧
          (false = true → ell < higherBandTargetScale d (j.val+3) N mu) ∧
          j.val+3 ≤ D ∧ 0 < higherBandRowMass d (j.val+3) D D q a b C lam ell
            (min ell (higherBandTargetScale d (j.val+3) N mu)) false
        exact ⟨hT1, (by intro h; cases h), (by have := j.isLt; omega), hp⟩
      have hzero : higherBandSignedRow d (higherBandFamilyTarget (j,false))
          (higherBandFamilyGuardDegree M (j,false)) D q a b C lam ell
          (higherBandFamilyUpper d ell N mu (j,false)) false = 0 := by
        exact higherBand_zero_mass_signed_zero d (j.val+3) D D q a b C lam ell _ hT1 false hz
      unfold higherBandFamilyRowIntegral
      rw [hzero]
      simp
    · have hzero : higherBandSignedRow d (higherBandFamilyTarget (j,false))
          (higherBandFamilyGuardDegree M (j,false)) D q a b C lam ell
          (higherBandFamilyUpper d ell N mu (j,false)) false = 0 := by
        exact higherBand_coarse_below_one_signed_zero d (j.val+3) D D q a b C lam ell _ (lt_min (by linarith) (hnu j)) (not_le.mp hT1)
      unfold higherBandFamilyRowIntegral
      rw [hzero]
      simp
  · simp only [higherBandPhysicalIntegral, ite_true, higherBandFamilyTarget]
    by_cases hactive : ell < higherBandTargetScale d (j.val+3) N mu
    · rw [ite_eq_left hactive]
      have hT1  := hell.trans hactive.le
      have hz : higherBandRowMass d (j.val+3) M D q a b C lam ell
          (higherBandTargetScale d (j.val+3) N mu) true = 0 := by
        have hn := higherBandRowMass_nonneg d (j.val+3) M D q a b C lam ell
          (higherBandTargetScale d (j.val+3) N mu) true
        apply le_antisymm _ hn
        apply le_of_not_gt
        intro hp
        apply hi
        change (1 ≤ higherBandTargetScale d (j.val+3) N mu) ∧
          (true = true → ell < higherBandTargetScale d (j.val+3) N mu) ∧
          j.val+3 ≤ M ∧ 0 < higherBandRowMass d (j.val+3) M D q a b C lam ell
            (higherBandTargetScale d (j.val+3) N mu) true
        exact ⟨hT1, fun _ => hactive, hFine j hactive, hp⟩
      have hzero : higherBandSignedRow d (higherBandFamilyTarget (j,true))
          (higherBandFamilyGuardDegree M (j,true)) D q a b C lam ell
          (higherBandFamilyUpper d ell N mu (j,true)) true = 0 := by
        exact higherBand_zero_mass_signed_zero d (j.val+3) M D q a b C lam ell _ hT1 true hz
      unfold higherBandFamilyRowIntegral
      rw [hzero]
      simp
    · rw [ite_eq_right hactive]
def higherBandPhysicalFirstAction  (ad bd lam ell N mu : ℝ)
    (D M q : ℕ) (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ)
    (i : Fin (D-2) × Bool) : ℝ :=
  if i.2 = true then
    if ell < higherBandTargetScale d (higherBandFamilyTarget i) N mu then
      higherBandFirstAction ad bd lam ell (higherBandFamilyUpper d ell N mu i)
        (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q C i.2 U p c Φ else 0
  else higherBandFirstAction ad bd lam ell (higherBandFamilyUpper d ell N mu i)
    (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q C i.2 U p c Φ
theorem integrated_cardinal_matrix_fin_cast {d n m D : ℕ} (h : m = n) (lam T : ℝ)
    (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam T (U ∘ finCongr h) β β' = integratedCardinalMatrix lam T U β β' := by
  subst n
  rfl
theorem integrated_cardinal_matrix_full_subset {d n D : ℕ} (lam T : ℝ)
    (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam T (spatialSubsetConfiguration Finset.univ U) β β' =
      integratedCardinalMatrix lam T U β β' := by
  let S : Finset (Fin n) := Finset.univ
  let h : S.card = n := by simp [S]
  let v : S ≃ Fin n := ⟨Subtype.val, fun j => ⟨j, Finset.mem_univ j⟩,
    (by intro j; rfl), (by intro j; rfl)⟩
  let τ : Equiv.Perm (Fin n) := ((finCongr h).symm.trans ((finCongr (Fintype.card_coe S).symm).trans (Fintype.equivFin S).symm)).trans v
  have hc : spatialSubsetConfiguration S U = (U ∘ τ) ∘ finCongr h := by
    funext j
    rfl
  rw [hc, integrated_cardinal_matrix_fin_cast h]
  exact integrated_cardinal_matrix_perm τ lam T U β β'
theorem higherBandFirstAction_target_count  (ad bd lam L T )
    (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam) (hL : 0 < L) (hT : 1 ≤ T)
    (m D q : ℕ) (hn : 2 ≤ n) (hD : 1 ≤ D) (hnD : n ≤ D) (hnm : n ≤ m)
    (C : ℝ) (fine : Bool) (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFirstAction ad bd lam L T n m D q C fine U p c Φ =
      (∏ i, p i) * responseMatrixAction q C (higherBandActualMatrix lam L T fine U) c Φ := by
  rw [higherBandFirstAction_actual_count_expansion ad bd lam L T ha hab hlam hL hT n m D q hn hD hnD
    C fine U hU p hp c Φ, densityCountCoefficient_exact ad bd ha hab m n n (by omega) le_rfl hnm]
  have h_higherBandActualMatrix_full_subset : (higherBandActualMatrix lam L T fine (spatialSubsetConfiguration Finset.univ U) : HighFrameIndex d D → _ → ℝ) =
      higherBandActualMatrix lam L T fine U := by
    funext β β'
    cases fine <;> simp only [higherBandActualMatrix, Bool.false_eq_true, ite_false, ite_true,
      globalCardinalBandMatrix, integrated_cardinal_matrix_full_subset]
  simp only [ite_true, by simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n)), Finset.sum_singleton, one_mul, h_higherBandActualMatrix_full_subset]
section Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end Matrix
def higherBandCoarseFirstAction  (ad bd lam ell N mu : ℝ)
    (r D q : ℕ) (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) : ℝ :=
  higherBandFirstAction ad bd lam ell (min ell (higherBandTargetScale d r N mu)) r D D q C false U p c Φ
def higherBandFineFirstAction  (ad bd lam ell N mu : ℝ)
    (r M D q : ℕ) (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) : ℝ :=
  if ell < higherBandTargetScale d r N mu then
    higherBandFirstAction ad bd lam ell (higherBandTargetScale d r N mu) r M D q C true U p c Φ else 0
end NearlyMinimax
