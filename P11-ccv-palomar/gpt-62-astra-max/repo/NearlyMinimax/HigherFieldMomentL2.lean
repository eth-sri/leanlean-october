module

public import NearlyMinimax.BoundedHyperplaneField
public import NearlyMinimax.SpatialLaplaceTail
public import NearlyMinimax.SpatialPairProductIntegration
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-! Actual spatial L² moments of the constructed bounded hyperplane field.
The estimate derives from its fair-sign occupancy law and genuine independent
spatial-coordinate integration. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

section
variable {d : ℕ} (T : ℝ) {j : ℕ} (q : CellMomentQuadruple j) (U : Fin j → Covariate d)

def boundedHyperplaneSpatialMoment : ℝ :=
  ∫ z, ∏ l, boundedHyperplaneFieldValue z (U l) ∂boundedHyperplaneFieldLaw d T

theorem boundedHyperplaneSpatialMoment_measurable (d : ℕ) [NeZero d] (T : ℝ) (j : ℕ) :
    Measurable (boundedHyperplaneSpatialMoment (d := d) T (j := j)) := by
  have hm : Measurable (fun Uz : (Fin j → Covariate d) × partitionFieldMark (Covariate d × ℝ) =>
      ∏ l, boundedHyperplaneFieldValue Uz.2 (Uz.1 l)) :=
    Finset.measurable_prod _ (fun l _ =>
      (boundedHyperplaneFieldValue_measurable d).comp
        (measurable_snd.prodMk ((measurable_pi_apply l).comp measurable_fst)))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem boundedHyperplaneSpatialMoment_abs_le_one [NeZero d]
    (T : ℝ) {j : ℕ} (U : Fin j → Covariate d) :
    |boundedHyperplaneSpatialMoment T U| ≤ 1 := by
  calc
    _ ≤ _ :=
      abs_integral_le_integral_abs
    _ = 1 := by simp [Finset.abs_prod, boundedHyperplaneFieldValue_abs,
      Finset.prod_const_one, integral_const, probReal_univ, smul_eq_mul, one_mul]

def spatialQuadDistance : ℝ :=
  exactEuclideanDistance (U (q.val 0)) (U (q.val 1)) +
    exactEuclideanDistance (U (q.val 2)) (U (q.val 3))

end

theorem spatialQuadDistance_continuous {d j : ℕ} (q : CellMomentQuadruple j) :
    Continuous (spatialQuadDistance (d := d) q) := by
  have hm01 : Continuous (fun U : Fin j → Covariate d => (U (q.val 0), U (q.val 1))) :=
    (continuous_apply (q.val 0)).prodMk (by fun_prop)
  have hm23 : Continuous (fun U : Fin j → Covariate d => (U (q.val 2), U (q.val 3))) :=
    (continuous_apply (q.val 2)).prodMk (by fun_prop)
  have h01 : Continuous (fun U : Fin j → Covariate d =>
      exactEuclideanDistance (U (q.val 0)) (U (q.val 1))) := by
    simpa only [Function.comp_def] using (exactEuclideanDistance_continuous).comp hm01
  exact h01.add (by
    simpa only [Function.comp_def] using (exactEuclideanDistance_continuous).comp hm23)

variable (d j : ℕ)

theorem spatialPatchBox_eq_hyperplaneCube :
    spatialPatchBox d = hyperplaneCube d := by
  ext x
  simp only [spatialPatchBox, mem_Icc, Pi.le_def, hyperplaneCube, mem_ofPred_eq, abs_le]
  aesop

/-- The true independent local-cube law has every coordinate in the source cube almost surely. -/
theorem spatialPatchProbability_pi_ae_cube :
    ∀ᵐ U ∂Measure.pi (fun _ : Fin j => spatialPatchProbability d),
      ∀ l, U l ∈ hyperplaneCube d := by
  apply ae_all_iff.mpr
  intro l
  exact (measurePreserving_eval (fun _ => spatialPatchProbability d) l).quasiMeasurePreserving.tendsto_ae.eventually
    (by rw [spatialPatchProbability, ← spatialPatchBox_eq_hyperplaneCube]; exact (ae_restrict_mem measurableSet_Icc).filter_mono (Measure.ae_smul_measure_le _))

/-- Genuine squared higher-moment bound under normalized independent spatial coordinates. -/
theorem boundedHyperplaneSpatialMoment_squared_probability_integral_le
    [NeZero d] {T : ℝ} (hT : 0 < T) {j : ℕ} (hj : 4 ≤ j) :
    (∫ U, (boundedHyperplaneSpatialMoment T U)^2
      ∂Measure.pi (fun _ : Fin j => spatialPatchProbability d)) ≤
      j^8 * (spatialExponentialConstant d / T^d)^2 := by
  classical
  let π := spatialPatchProbability d
  let μ := Measure.pi (fun _ : Fin j => π)
  let a : ℝ := Fintype.card (CellMomentQuadruple j)
  let E : CellMomentQuadruple j → (Fin j → Covariate d) → ℝ :=
    fun q U => Real.exp (-(T * spatialQuadDistance q U))
  have hem q : Measurable (E q) :=
    (spatialQuadDistance_continuous q |>.const_mul T |>.neg |>.rexp).measurable
  have hei q : Integrable (E q) μ :=
    Integrable.of_bound (hem q).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun U => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hT.le (add_nonneg (exactEuclideanDistance_nonneg _ _) (exactEuclideanDistance_nonneg _ _)))))
  have hmi : Integrable (fun U => (boundedHyperplaneSpatialMoment T U)^2) μ :=
    Integrable.of_bound ((boundedHyperplaneSpatialMoment_measurable d T j).pow_const 2).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun U => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [boundedHyperplaneSpatialMoment_abs_le_one T U, abs_nonneg (boundedHyperplaneSpatialMoment T U),
          sq_abs (boundedHyperplaneSpatialMoment T U)])
  have hpoint : ∀ᵐ U ∂μ, (boundedHyperplaneSpatialMoment T U)^2 ≤ a * ∑ q, E q U := by
    filter_upwards [spatialPatchProbability_pi_ae_cube d j] with U hU
    have hb := boundedHyperplaneField_higher_moment_envelope hT.le hj hU
    simp_rw [← exactEuclideanDistance_eq_euclideanNorm] at hb
    change |boundedHyperplaneSpatialMoment T U| ≤
      ∑ q, Real.exp (-T / 2 * spatialQuadDistance q U) at hb
    have hs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun q => Real.exp (-T / 2 * spatialQuadDistance q U))
    have hsq : (boundedHyperplaneSpatialMoment T U)^2 ≤
        (∑ q, Real.exp (-T / 2 * spatialQuadDistance q U))^2 := by
      nlinarith [sq_abs (boundedHyperplaneSpatialMoment T U), abs_nonneg (boundedHyperplaneSpatialMoment T U)]
    have heq q :
        Real.exp (-T / 2 * spatialQuadDistance q U)^2 = E q U := by
      rw [← Real.exp_nat_mul]
      apply congrArg Real.exp
      ring
    exact hsq.trans (by simpa only [Finset.card_univ, heq] using hs)
  have hpair q : (∫ U, E q U ∂μ) ≤ (spatialExponentialConstant d / T^d)^2 := by
    rw [show (∫ U, E q U ∂μ) =
        (∫ xy, Real.exp (-(T*exactEuclideanDistance xy.1 xy.2)) ∂π.prod π)^2 from
      spatialPi_two_pairs_integral_factor π ⟨q.val,q.property⟩ T]
    have hb := spatial_probability_pair_exponential_integral_le (NeZero.pos d) (spatialPatchProbability_le_volume d) hT
    gcongr
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hac : a ≤ j^4 := by
    dsimp [a]
    exact_mod_cast (by simpa using Fintype.card_subtype_le (fun q : Fin 4 → Fin j => Function.Injective q))
  calc
    _ ≤ _ :=
      integral_mono_ae hmi ((integrable_finsetSum _ (fun q _ => hei q)).const_mul a) hpoint
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun q _ => hei q)]
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q _ => hpair q)) ha
    _ = a^2 * (spatialExponentialConstant d / T^d)^2 := by simp; ring
    _ ≤ _ := by
      have hb : a^2 ≤ j^8 := by
        simpa only [← pow_mul] using pow_le_pow_left₀ ha hac 2
      bound

/-- The actual source cube volume is its volume times the genuine uniform law. -/
theorem spatialPatchVolume_eq_smulProbability :
    volume.restrict (spatialPatchBox d) = (2 : ℝ≥0∞)^d • spatialPatchProbability d := by
  rw [spatialPatchProbability, smul_smul, ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_smul]

/-- The genuine unnormalized source-cube product integral with the exact volume factor. -/
theorem boundedHyperplaneSpatialMoment_squared_cube_integral_le
    [NeZero d] {T : ℝ} (hT : 0 < T) {j : ℕ} (hj : 4 ≤ j) :
    (∫ U, (boundedHyperplaneSpatialMoment T U)^2
      ∂Measure.pi (fun _ : Fin j => volume.restrict (spatialPatchBox d))) ≤
      2^(d*j) * j^8 * (spatialExponentialConstant d / T^d)^2 := by
  let : IsFiniteMeasure ((2 : ℝ≥0∞)^d • spatialPatchProbability d) := by
    rw [← spatialPatchVolume_eq_smulProbability]
    infer_instance
  have he : Measure.pi (fun _ => volume.restrict (spatialPatchBox d)) =
      ((2 : ℝ≥0∞)^d)^j • Measure.pi (fun _ : Fin j => spatialPatchProbability d) := by
    simp [spatialPatchVolume_eq_smulProbability]
    simpa using spatialPi_const_smul (J := Fin j) (spatialPatchProbability d) (2^d)
  rw [he, integral_smul_measure]
  simp [ENNReal.toReal_pow, ENNReal.toReal_ofNat, smul_eq_mul, ← pow_mul]
  convert mul_le_mul_of_nonneg_left (boundedHyperplaneSpatialMoment_squared_probability_integral_le d hT hj) (by positivity : 0 ≤ (2 : ℝ)^(d*j)) using 1; ring

/-- A fixed dimension constant for the actual higher-moment spatial L² estimate. -/
def hyperplaneSpatialMomentConstant : ℝ :=
  2^d * (1 + spatialExponentialConstant d)

theorem hyperplaneSpatialMomentConstant_positive :
    0 < hyperplaneSpatialMomentConstant d := by
  unfold hyperplaneSpatialMomentConstant
  have := spatialExponentialConstant_nonneg d
  positivity

/-- The paper's higher-moment L² estimate for the genuinely constructed field,
with no spatial-moment or integral bound as a premise. -/
theorem boundedHyperplaneSpatialMoment_L2_le
    [NeZero d] {T : ℝ} (hT : 0 < T) {j : ℕ} (hj : 4 ≤ j) :
    Real.sqrt (∫ U, (boundedHyperplaneSpatialMoment T U)^2
      ∂Measure.pi (fun _ : Fin j => volume.restrict (spatialPatchBox d))) ≤
      (hyperplaneSpatialMomentConstant d)^j * j^4 / T^d := by
  let C := spatialExponentialConstant d
  have hC  := spatialExponentialConstant_nonneg d
  have hC1 : 1 ≤ 1+C := by linarith
  have hV : 2^(d*j) ≤ ((2 : ℝ)^d)^(2*j) := by
    rw [pow_mul]
    exact pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (by omega)
  have hCp : C^2 ≤ (1+C)^(2*j) := le_trans (by bound) (pow_le_pow_right₀ hC1 (by omega))
  have hconstant : 2^(d*j) * C^2 ≤ (hyperplaneSpatialMomentConstant d)^(2*j) := by
    unfold hyperplaneSpatialMomentConstant
    rw [mul_pow]
    bound
  have hupper : 2^(d*j) * j^8 * (C/T^d)^2 ≤
      ((hyperplaneSpatialMomentConstant d)^j * j^4 / T^d)^2 := by
    have ht := mul_le_mul_of_nonneg_right hconstant (show 0 ≤ j^8 / (T^d)^2 by positivity)
    convert ht using 1 <;> simp [div_pow, mul_pow, ← pow_mul] <;> ring
  exact Real.sqrt_le_iff.mpr ⟨by positivity [hyperplaneSpatialMomentConstant_positive d], (boundedHyperplaneSpatialMoment_squared_cube_integral_le d hT hj).trans hupper⟩

end NearlyMinimax
