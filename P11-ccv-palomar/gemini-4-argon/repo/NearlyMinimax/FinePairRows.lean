module
public import NearlyMinimax.CardinalSeparatedKernel
public import Mathlib
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import NearlyMinimax.HighUnionReset
public import NearlyMinimax.HighLocalFrame
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
section
open MeasureTheory Set MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {d n F : ℕ}
section
variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace Z]
def highSeparatedDerivativeBudget (a ρ : ℝ) : ℝ :=
  4 * (((2 * ρ + a) / a ^ 2) ^ 2 + 2 / a ^ 2)
theorem high_response_variance_correction_abs_bound  (hn : 1 ≤ n)
    (a V η pPlus ) (ha : 0 < a) (hpPlus : 0 ≤ pPlus)
    (p g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hw : ∀ i, |w i| ≤ 1) (hIncoming : ∀ i, |p i| ≤ pPlus)
    (hp : ∀ i u, 0 ≤ ternaryMass a (coefficientRegression η g w φ c i) V u)
    (y : Fin n → Fin 3) :
    |η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i| ≤
      pPlus ^ n * (1 / a ^ 2) * (n : ℝ) ^ 2 * η ^ 2 := by
  have hvar : |∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i| ≤
      (n : ℝ) / a ^ 2 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i : Fin n, 1 / a ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        exact (mul_le_mul (by simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hw i) 2)
          (high_response_variance_term_abs_bound a V η ha g w φ c hp y i)
          (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)
      _ = _ := by simp [div_eq_mul_inv]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith only [hn1]
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg η)]
  calc
    _ ≤ η ^ 2 * pPlus ^ n * ((n : ℝ) / a ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left
        (finite_density_product_abs_bound p pPlus hpPlus hIncoming) (sq_nonneg η))
        hvar (abs_nonneg _) (by positivity)
    _ ≤ η ^ 2 * pPlus ^ n * ((n : ℝ) ^ 2 / a ^ 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnsq (sq_nonneg a)) (by positivity)
    _ = _ := by ring
def highSeparatedScoreExponentialConstant (a ρ pPlus pMinus cMass : ℝ) : ℝ :=
  4 * max 1 (pPlus / (pMinus * cMass)) *
    max 1 (highSeparatedDerivativeBudget a ρ + 1 / a ^ 2)
theorem highSeparated_score_budget_absorb (n : ℕ) (hn : 1 ≤ n)
    (a ρ pPlus pMinus cMass η B : ℝ) (hpPlus : 0 ≤ pPlus)
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass) (hB : 0 ≤ B) :
    (pPlus / (pMinus * cMass)) ^ n *
      (highSeparatedDerivativeBudget a ρ * B + 1 / a ^ 2) * (n : ℝ) ^ 2 * η ^ 2 ≤
      (highSeparatedScoreExponentialConstant a ρ pPlus pMinus cMass) ^ n *
        η ^ 2 * (B + 1) := by
  let R : ℝ := max 1 (pPlus / (pMinus * cMass))
  let K : ℝ := max 1 (highSeparatedDerivativeBudget a ρ + 1 / a ^ 2)
  have hR1 : 1 ≤ R := le_max_left _ _
  have hK1 : 1 ≤ K := le_max_left _ _
  have h_highSeparatedDerivativeBudget_nonneg : 0 ≤ highSeparatedDerivativeBudget a ρ := by
    unfold highSeparatedDerivativeBudget
    positivity
  have hder := h_highSeparatedDerivativeBudget_nonneg
  have hK : highSeparatedDerivativeBudget a ρ * B + 1 / a ^ 2 ≤ K * (B + 1) := by
    have hk : highSeparatedDerivativeBudget a ρ + 1 / a ^ 2 ≤ K := le_max_right _ _
    have hz : 0 ≤ 1 / a ^ 2 := by positivity
    nlinarith only [hk, hB, hder, hz, mul_nonneg hB hz]
  have hnNat := Nat.two_mul_sq_add_one_le_two_pow_two_mul n
  have hnReal : (2 : ℝ) * (n : ℝ) ^ 2 + 1 ≤ 2 ^ (2 * n) := by exact_mod_cast hnNat
  have hnsq : (n : ℝ) ^ 2 ≤ (4 : ℝ) ^ n := by
    have he : (2 : ℝ) ^ (2 * n) = (4 : ℝ) ^ n := by rw [pow_mul]; norm_num
    rw [he] at hnReal
    nlinarith only [hnReal, sq_nonneg (n : ℝ)]
  have hRpow : (pPlus / (pMinus * cMass)) ^ n ≤ R ^ n :=
    pow_le_pow_left₀ (div_nonneg hpPlus (mul_pos hpMinus hcMass).le) (le_max_right _ _) _
  have hKpow : K ≤ K ^ n := le_self_pow₀ hK1 (by omega)
  calc
    _ ≤ (R ^ n * (K * (B + 1))) * 4 ^ n * η ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul hRpow hK (by positivity) (by positivity)) hnsq
          (sq_nonneg _) (by positivity)) (sq_nonneg η)
    _ ≤ (R ^ n * (K ^ n * (B + 1))) * 4 ^ n * η ^ 2 := by
      gcongr
    _ = _ := by
      dsimp [highSeparatedScoreExponentialConstant, R, K]
      simp only [mul_pow]
      ring
end
def highCardinalDensityReset  (ad bd lam : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (ζ : CardinalSeparatedMark d n) (z : ℝ) (ε : Fin n → ℝ) (i : Fin n) : ℝ :=
  localDensityReset ad bd n z ε p (fun i l => cardinalSeparatedFactor lam ζ l (U i)) i
theorem high_response_matrix_two_general  [Fintype ι] [DecidableEq ι]
    (q ) (hq : 2 ≤ q) (C a V η A)
    (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i)
    (g w φ) (c : ι → ℝ) (y : Fin 2 → Fin 3) :
    responseMatrixAction q C A c (fun v => highResponseProduct a V η g w φ v y) =
      η ^ 2 * (w 0) ^ 2 * spatialFrameCovariance A φ 0 0 * highResponseVarianceTerm a V η g w φ c y 0 +
      η ^ 2 * (w 1) ^ 2 * spatialFrameCovariance A φ 1 1 * highResponseVarianceTerm a V η g w φ c y 1 +
      η ^ 2 * w 0 * w 1 * spatialFrameCovariance A φ 0 1 *
        ternaryMeanDerivative a (coefficientRegression η g w φ c 0) (y 0) *
        ternaryMeanDerivative a (coefficientRegression η g w φ c 1) (y 1) := by
  let δ := coefficientDirection η w φ c
  let f := coefficientRegression η g w φ c
  let m := fun i => ternaryMeanDerivative a (f i) (y i)
  let e := fun i => highResponseVarianceTerm a V η g w φ c y i
  have he0 : ({0, 1} : Finset (Fin 2)).erase 0 = {1} := by decide
  have he1 : ({0, 1} : Finset (Fin 2)).erase 1 = {0} := by decide
  have hs (v : ι → ℝ) : finiteProductSecond Finset.univ
      (fun i z => ternaryMass a (f i + z * δ v i) V (y i))
      (fun i z => δ v i * ternaryMeanDerivative a (f i + z * δ v i) (y i))
      (fun i _ => (δ v i) ^ 2 * ternaryMeanSecondDerivative a (y i)) 0 =
      2 * e 0 * (δ v 0 * δ v 0) + (2 * e 1) * (δ v 1 * δ v 1) +
        (2 * m 0 * m 1) * (δ v 0 * δ v 1) := by
    simp [finiteProductSecond, Finset.univ_fin2, he0, he1, e, highResponseVarianceTerm,
      ternary_heat_identity, m, f]
    ring
  rw [high_response_matrix_second q hq C a V η A g w φ c y]
  change (1 / 2 ) * covarianceAction C A
    (fun v => finiteProductSecond Finset.univ
      (fun i z => ternaryMass a (f i + z * δ v i) V (y i))
      (fun i z => δ v i * ternaryMeanDerivative a (f i + z * δ v i) (y i))
      (fun i _ => (δ v i) ^ 2 * ternaryMeanSecondDerivative a (y i)) 0) = _
  simp_rw [hs]
  rw [covarianceAction_add, covarianceAction_add]
  simp_rw [covarianceAction_mul]
  rw [covariance_direction_product C η A hC hA w φ c 0 0,
    covariance_direction_product C η A hC hA w φ c 1 1,
    covariance_direction_product C η A hC hA w φ c 0 1]
  dsimp [m, f, e]
  ring
def finePairCoordinatePolynomial  (l : Fin d) : MvPolynomial (Fin d) ℝ := C 8 * X l
def finePairSquarePolynomial (d ) : MvPolynomial (Fin d) ℝ :=
  ∑ l, (finePairCoordinatePolynomial l) ^ 2
theorem finePairCoordinatePolynomial_degree  (l : Fin d) :
    (finePairCoordinatePolynomial l).totalDegree ≤ 1 := (totalDegree_mul _ _).trans (by simp [finePairCoordinatePolynomial])
theorem finePairCoordinatePolynomial_eval  (l : Fin d) (x : Covariate d) :
    eval (fun r => x r / 8) (finePairCoordinatePolynomial l) = x l := by
  simp only [finePairCoordinatePolynomial, map_mul, eval_C, eval_X]
  ring
def finePairUnitMatrix (d F ) (β β' : HighFrameIndex d F) : ℝ :=
  highFrameCoefficients (1 : MvPolynomial (Fin d) ℝ) β * highFrameCoefficients 1 β'
def finePairDistanceMatrix (d F ) (β β' : HighFrameIndex d F) : ℝ :=
  (∑ l : Fin d, 2 * highFrameCoefficients (finePairCoordinatePolynomial l) β *
    highFrameCoefficients (finePairCoordinatePolynomial l) β') -
    highFrameCoefficients (finePairSquarePolynomial d) β * highFrameCoefficients 1 β' -
    highFrameCoefficients (1 : MvPolynomial (Fin d) ℝ) β *
      highFrameCoefficients (finePairSquarePolynomial d) β'
theorem finePairUnitMatrix_symmetric (d F β β') :
    finePairUnitMatrix d F β β' = finePairUnitMatrix d F β' β := mul_comm _ _
theorem spatial_frame_covariance_outer  [Fintype κ] [DecidableEq κ]
     (u v : κ → ℝ) (φ : Fin n → κ → ℝ) (i j : Fin n) :
    spatialFrameCovariance (fun β β' => u β * v β') φ i j =
      (∑ β, φ i β * u β) * (∑ β, φ j β * v β) := by
  simp only [spatialFrameCovariance, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro β' _
  ring
theorem spatial_frame_covariance_sub  [Fintype κ] [DecidableEq κ]
     (A B ) (φ : Fin n → κ → ℝ) (i j : Fin n) :
    spatialFrameCovariance (fun β β' => A β β' - B β β') φ i j =
      spatialFrameCovariance A φ i j - spatialFrameCovariance B φ i j := by
  simp only [spatialFrameCovariance, mul_sub, Finset.sum_sub_distrib]
theorem finePairUnitMatrix_kernel  (U : Fin n → Covariate d) (i j : Fin n) :
    spatialFrameCovariance (finePairUnitMatrix d F) (fun l => highFrameFeature (U l)) i j = 1 := by
  unfold finePairUnitMatrix
  rw [spatial_frame_covariance_outer]
  have he (x : Covariate d) : (∑ β : HighFrameIndex d F,
      highFrameFeature x β * highFrameCoefficients (1 : MvPolynomial (Fin d) ℝ) β) = 1 := by
    simpa only [map_one] using (high_frame_polynomial_evaluation (1 : MvPolynomial (Fin d) ℝ)
      (by simp) x).symm
  rw [he, he, one_mul]
theorem finePairDistanceMatrix_kernel  (hF : 3 ≤ F)
    (U : Fin n → Covariate d) (i j : Fin n) :
    spatialFrameCovariance (finePairDistanceMatrix d F) (fun l => highFrameFeature (U l)) i j =
      -spatialSquaredDistance (U i) (U j) := by
  have hc (x : Covariate d) : (∑ β : HighFrameIndex d F,
      highFrameFeature x β * highFrameCoefficients (1 : MvPolynomial (Fin d) ℝ) β) = 1 := by
    simpa only [map_one] using (high_frame_polynomial_evaluation (1 : MvPolynomial (Fin d) ℝ)
      (by simp) x).symm
  have hl (x : Covariate d) (l : Fin d) : (∑ β : HighFrameIndex d F,
      highFrameFeature x β * highFrameCoefficients (finePairCoordinatePolynomial l) β) = x l := by
    exact (high_frame_polynomial_evaluation (finePairCoordinatePolynomial l)
      ((finePairCoordinatePolynomial_degree l).trans (by omega)) x).symm.trans
        (finePairCoordinatePolynomial_eval l x)
  have hs (x : Covariate d) : (∑ β : HighFrameIndex d F,
      highFrameFeature x β * highFrameCoefficients (finePairSquarePolynomial d) β) = ∑ l, (x l) ^ 2 := by
    have h_finePairSquarePolynomial_degree : (finePairSquarePolynomial d).totalDegree ≤ 2 := by
      apply (totalDegree_finsetSum _ _).trans
      apply Finset.sup_le
      intro l _
      exact (totalDegree_pow _ _).trans (by nlinarith only [finePairCoordinatePolynomial_degree l])
    exact (high_frame_polynomial_evaluation (finePairSquarePolynomial d)
      (h_finePairSquarePolynomial_degree.trans (by omega)) x).symm.trans
        (by simp only [finePairSquarePolynomial, map_sum, map_pow, finePairCoordinatePolynomial_eval])
  unfold finePairDistanceMatrix
  rw [spatial_frame_covariance_sub, spatial_frame_covariance_sub,
    spatial_frame_covariance_sum]
  simp_rw [spatial_frame_covariance_rank_one, spatial_frame_covariance_outer, hc, hl, hs]
  simp only [mul_one, one_mul, spatialSquaredDistance, ← Finset.sum_sub_distrib]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring
def finePairCombinedMatrix (d F ) (W : ℝ) (β β' : HighFrameIndex d F) : ℝ :=
  finePairUnitMatrix d F β β' + W * finePairDistanceMatrix d F β β'
theorem finePairCombinedMatrix_symmetric (d F W β β') :
    finePairCombinedMatrix d F W β β' = finePairCombinedMatrix d F W β' β := by
  have h_finePairDistanceMatrix_symmetric : finePairDistanceMatrix d F β β' = finePairDistanceMatrix d F β' β := by
    unfold finePairDistanceMatrix
    have hs : (∑ l : Fin d, 2 * highFrameCoefficients (finePairCoordinatePolynomial l) β *
        highFrameCoefficients (finePairCoordinatePolynomial l) β') =
        ∑ l : Fin d, 2 * highFrameCoefficients (finePairCoordinatePolynomial l) β' *
          highFrameCoefficients (finePairCoordinatePolynomial l) β :=
      Finset.sum_congr rfl (fun l _ => by ring)
    rw [hs]
    ring
  simp only [finePairCombinedMatrix, finePairUnitMatrix_symmetric d F β β',
    h_finePairDistanceMatrix_symmetric]
theorem spatial_frame_covariance_scalar  [Fintype κ] [DecidableEq κ]
     (A : κ → κ → ℝ) (W : ℝ) (φ : Fin n → κ → ℝ) (i j : Fin n) :
    spatialFrameCovariance (fun β β' => W * A β β') φ i j = W * spatialFrameCovariance A φ i j := by
  simp only [spatialFrameCovariance, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro β' _
  ring
theorem finePairCombinedMatrix_kernel  (hF : 3 ≤ F) (W )
    (U : Fin n → Covariate d) (i j : Fin n) :
    spatialFrameCovariance (finePairCombinedMatrix d F W) (fun l => highFrameFeature (U l)) i j =
      1 - W * spatialSquaredDistance (U i) (U j) := by
  unfold finePairCombinedMatrix
  rw [spatial_frame_covariance_add, spatial_frame_covariance_scalar,
    finePairUnitMatrix_kernel, finePairDistanceMatrix_kernel hF]
  ring
end NearlyMinimax
end
open MeasureTheory ProbabilityTheory Set Polynomial
open scoped ENNReal BigOperators NNReal RealInnerProductSpace
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section
section
variable {d : ℕ}
section
def fairSignValue (b : Fin 2) : ℝ := if b = 0 then 1 else -1
def fairSignLaw : Measure (Fin 2) :=
  ENNReal.ofReal (1 / 2 ) • Measure.dirac 0 +
    ENNReal.ofReal (1 / 2 ) • Measure.dirac 1
instance fairSignLaw_probability : IsProbabilityMeasure fairSignLaw := by
  constructor
  simp only [fairSignLaw, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num
theorem fairSign_integral (f : Fin 2 → ℝ) :
    (∫ b, f b ∂fairSignLaw) = (f 0 + f 1) / 2 := by
  unfold fairSignLaw
  rw [integral_add_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    norm_num
    ring
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
theorem fairSignValue_abs (b ) : |fairSignValue b| = 1 := by
  fin_cases b <;> norm_num [fairSignValue]
theorem fairSignValue_sq (b ) : fairSignValue b ^ 2 = 1 := by
  fin_cases b <;> norm_num [fairSignValue]
theorem fairSign_power_moment (k : ℕ) :
    (∫ b, fairSignValue b ^ k ∂fairSignLaw) = if Even k then 1 else 0 := by
  rw [fairSign_integral]
  simp only [fairSignValue]
  norm_num
  by_cases h : Even k
  · simp [h, h.neg_one_pow]
  · have ho  := Nat.not_even_iff_odd.mp h
    simp [h, ho.neg_one_pow]
def cellSignLaw (I ) [Fintype I] : Measure (I → Fin 2) :=
  Measure.pi (fun _ => fairSignLaw)
instance cellSignLaw_probability (I : Type*) [Fintype I] :
    IsProbabilityMeasure (cellSignLaw I) := by
  unfold cellSignLaw
  infer_instance
theorem cellSign_covariance  [Fintype I] [DecidableEq I] (i j ) :
    (∫ b, fairSignValue (b i) * fairSignValue (b j) ∂cellSignLaw I) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [← pow_two, fairSignValue_sq]
    simp
  · have hi : IndepFun (fun b => b i) (fun b => b j)
        (cellSignLaw I) := by
      exact (iIndepFun_pi (fun _ => measurable_id.aemeasurable)).indepFun hij
    rw [hi.integral_fun_comp_mul_comp (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply j).aemeasurable (Measurable.of_discrete.aestronglyMeasurable)
      (Measurable.of_discrete.aestronglyMeasurable)]
    have h_cellSign_mean : (∫ b, fairSignValue (b i) ∂cellSignLaw I) = 0 := by
      change (∫ b, fairSignValue (b i) ∂Measure.pi (fun _ => fairSignLaw)) = 0
      rw [integral_comp_eval (μ := fun _ : I => fairSignLaw)
        (f := fairSignValue) (i := i) (by fun_prop), fairSign_integral]
      norm_num [fairSignValue]
    simp [h_cellSign_mean, hij]
theorem cellSign_product_power_moment {I : Type*} [Fintype I] (k : I → ℕ) :
    (∫ b, ∏ i, fairSignValue (b i) ^ k i ∂cellSignLaw I) =
      ∏ i, if Even (k i) then ↑1 else 0 := by
  change (∫ b, ∏ i, fairSignValue (b i) ^ k i
    ∂Measure.pi (fun _ : I => fairSignLaw)) = _
  rw [integral_fintype_prod_eq_prod (fun i b => fairSignValue b ^ k i)]
  simp_rw [fairSign_power_moment]
theorem cellSign_product_moment  [Fintype I] [Fintype J]
    [DecidableEq I] (p : J → I) :
    (∫ b, ∏ j, fairSignValue (b (p j)) ∂cellSignLaw I) =
      if ∀ i, Even ((Finset.univ.filter (fun j => p j = i)).card) then ↑1 else 0 := by
  have he (b : I → Fin 2) : (∏ j, fairSignValue (b (p j))) =
      ∏ i, fairSignValue (b i) ^ (Finset.univ.filter (fun j => p j = i)).card := by
    rw [← Finset.prod_fiberwise_of_maps_to' (s := Finset.univ) (t := Finset.univ)
      (g := p) (fun _ _ => Finset.mem_univ _) (fun i => fairSignValue (b i))]
    simp only [Finset.prod_const]
  simp_rw [he]
  rw [cellSign_product_power_moment, Fintype.prod_boole]
abbrev partitionFieldFiber (H : Type*) (n : ℕ) :=
  (Fin n → H) × ((Fin n → Fin 2) → Fin 2)
abbrev partitionFieldMark (H : Type*) := Σ n : ℕ, partitionFieldFiber H n
variable {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
theorem measurable_variable_finite_eval  [MeasurableSpace E]
    [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] [MeasurableSpace B]
    (g : E → I → B) (p : E → I) (hg : Measurable g) (hp : Measurable p) :
    Measurable (fun z => g z (p z)) := by
  intro s hs
  have he : (fun z => g z (p z)) ⁻¹' s =
      ⋃ i, (p ⁻¹' {i}) ∩ ((fun z => g z i) ⁻¹' s) := by
    ext z
    simp
  rw [he]
  exact MeasurableSet.iUnion (fun i =>
    (hp (measurableSet_singleton i)).inter ((hg.eval) hs))
def partitionFieldFiberLaw (μ : Measure H) (n ) : Measure (partitionFieldFiber H n) :=
  (Measure.pi (fun _ => μ)).prod (cellSignLaw (Fin n → Fin 2))
instance partitionFieldFiberLaw_probability (μ : Measure H) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (partitionFieldFiberLaw μ n) := by
  unfold partitionFieldFiberLaw
  infer_instance
def poissonCellFieldLaw (μ : Measure H) (r : ℝ≥0) : Measure (partitionFieldMark H) :=
  Measure.sum fun n => ENNReal.ofReal (Real.exp (-r) * r ^ n / n.factorial) •
    (partitionFieldFiberLaw μ n).map (Sigma.mk n)
instance poissonCellFieldLaw_probability (μ : Measure H) [IsProbabilityMeasure μ] (r : ℝ≥0) :
    IsProbabilityMeasure (poissonCellFieldLaw μ r) := by
  constructor
  simp only [poissonCellFieldLaw, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, smul_eq_mul]
  have hm n : (partitionFieldFiberLaw μ n).map (Sigma.mk n) Set.univ = 1 := by
    rw [Measure.map_apply (measurable_sigma_mk_actual n) MeasurableSet.univ]
    simp
  simp_rw [hm, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    (hasSum_one_poissonMeasure r).summable, (hasSum_one_poissonMeasure r).tsum_eq]
  simp
theorem poissonCellFieldLaw_measurable (μ : Measure H) :
    Measurable (poissonCellFieldLaw μ) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [poissonCellFieldLaw, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
  apply Measurable.ennreal_tsum
  intro n
  apply Measurable.mul_const
  apply ENNReal.measurable_ofReal.comp
  exact ((measurable_coe_nnreal_real.neg.exp).mul
    (measurable_coe_nnreal_real.pow_const n)).div_const _
instance partitionFieldMark_standardBorel [StandardBorelSpace H] :
    StandardBorelSpace (partitionFieldMark H) := sigma_standardBorel_actual
def partitionFieldPattern (ρ : H → X → Fin 2) 
    (h : Fin n → H) (x : X) : Fin n → Fin 2 := fun i => ρ (h i) x
def partitionFieldFiberValue (ρ : H → X → Fin 2) 
    (z : partitionFieldFiber H n) (x : X) : ℝ :=
  fairSignValue (z.2 (partitionFieldPattern ρ z.1 x))
def poissonCellFieldValue (ρ : H → X → Fin 2)
    (z : partitionFieldMark H) (x : X) : ℝ := partitionFieldFiberValue ρ z.2 x
theorem partitionFieldFiberValue_abs (ρ : H → X → Fin 2) {n : ℕ}
    (z : partitionFieldFiber H n) (x : X) : |partitionFieldFiberValue ρ z x| = 1 :=
  fairSignValue_abs _
theorem poissonCellFieldValue_abs (ρ : H → X → Fin 2)
    (z : partitionFieldMark H) (x : X) : |poissonCellFieldValue ρ z x| = 1 :=
  partitionFieldFiberValue_abs _ _ _
theorem partitionFieldPattern_measurable (ρ )
    (hρ : Measurable (Function.uncurry ρ)) (n ) :
    Measurable (fun z : (Fin n → H) × X => partitionFieldPattern ρ z.1 z.2) := by
  apply Measurable.of_eval
  intro i
  change Measurable (fun z : (Fin n → H) × X => ρ (z.1 i) z.2)
  have he : Measurable (fun z : (Fin n → H) × X => (z.1 i, z.2)) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
  exact hρ.comp he
theorem partitionFieldFiberValue_measurable (ρ )
    (hρ : Measurable (Function.uncurry ρ)) (n ) :
    Measurable (fun z : partitionFieldFiber H n × X =>
      partitionFieldFiberValue ρ z.1 z.2) := by
  unfold partitionFieldFiberValue
  have hp : Measurable (fun z : partitionFieldFiber H n × X =>
      partitionFieldPattern ρ z.1.1 z.2) :=
    (partitionFieldPattern_measurable ρ hρ n).comp
      (measurable_fst.fst.prodMk measurable_snd)
  exact (Measurable.of_discrete : Measurable fairSignValue).comp
    (measurable_variable_finite_eval _ _ (measurable_fst.snd) hp)
theorem partitionFieldFiberValue_measurable_fixed (ρ : H → X → Fin 2)
    (hρ : Measurable (Function.uncurry ρ)) (n : ℕ) (x : X) :
    Measurable (fun z : partitionFieldFiber H n => partitionFieldFiberValue ρ z x) :=
  (partitionFieldFiberValue_measurable ρ hρ n).comp (measurable_id.prodMk measurable_const)
theorem poissonCellFieldValue_measurable_fixed (ρ : H → X → Fin 2)
    (hρ : Measurable (Function.uncurry ρ)) (x : X) :
    Measurable (fun z : partitionFieldMark H => poissonCellFieldValue ρ z x) := measurable_sigma_of_fibers _ (fun n => partitionFieldFiberValue_measurable_fixed ρ hρ n x)
theorem poissonCellField_integral_series (μ ) [IsProbabilityMeasure μ]
    (r : ℝ≥0) (f : partitionFieldMark H → ℝ) (hf : Measurable f)
    (hfbound : ∀ z, |f z| ≤ 1) :
    (∫ z, f z ∂poissonCellFieldLaw μ r) =
      ∑' n, (Real.exp (-r) * r ^ n / n.factorial) *
        ∫ z, f ⟨n, z⟩ ∂partitionFieldFiberLaw μ n := by
  have hi : Integrable f (poissonCellFieldLaw μ r) :=
    Integrable.of_bound hf.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hfbound z))
  rw [poissonCellFieldLaw, integral_sum_measure hi]
  apply tsum_congr
  intro n
  rw [integral_smul_measure, integral_map (measurable_sigma_mk_actual n).aemeasurable
    hf.aestronglyMeasurable]
  have hw : 0 ≤ Real.exp (-r) * r ^ n / n.factorial := by positivity
  simp only [ENNReal.toReal_ofReal hw, smul_eq_mul]
theorem poissonCellFieldValue_measurable [StandardBorelSpace H] [StandardBorelSpace X]
    (ρ ) (hρ : Measurable (Function.uncurry ρ)) :
    Measurable (fun z : partitionFieldMark H × X => poissonCellFieldValue ρ z.1 z.2) := by
  letI : TopologicalSpace H := (upgradeStandardBorel H).toTopologicalSpace
  letI : BorelSpace H := (upgradeStandardBorel H).toBorelSpace
  letI : TopologicalSpace X := (upgradeStandardBorel X).toTopologicalSpace
  letI : BorelSpace X := (upgradeStandardBorel X).toBorelSpace
  letI : BorelSpace (partitionFieldMark H) := sigma_borelSpace_actual
  letI : BorelSpace (Σ n : ℕ, partitionFieldFiber H n × X) := sigma_borelSpace_actual
  have hf : Measurable (fun z : Σ n : ℕ, partitionFieldFiber H n × X =>
      partitionFieldFiberValue ρ z.2.1 z.2.2) :=
    measurable_sigma_of_fibers _ (partitionFieldFiberValue_measurable ρ hρ)
  exact hf.comp (Homeomorph.sigmaProdDistrib.measurable)
def partitionSameProbability (μ : Measure H) (ρ : H → X → Fin 2) (x y : X) : ℝ :=
  ∫ h, if ρ h x = ρ h y then 1 else 0 ∂μ
theorem poisson_weighted_power_hasSum (r p) :
    HasSum (fun n => (Real.exp (-r) * r ^ n / n.factorial) * p ^ n)
      (Real.exp (-r * (1 - p))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (r * p)).mul_left
    (Real.exp (-r))
  convert h using 1
  · ext n
    rw [mul_pow]
    ring
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    congr 1
    ring
theorem poissonCellField_covariance (μ ) [IsProbabilityMeasure μ]
    (r ) (ρ : H → X → Fin 2) (hρ : Measurable (Function.uncurry ρ)) (x y : X) :
    (∫ z, poissonCellFieldValue ρ z x * poissonCellFieldValue ρ z y
      ∂poissonCellFieldLaw μ r) =
        Real.exp (-↑r * (1 - partitionSameProbability μ ρ x y)) := by
  rw [poissonCellField_integral_series μ r (fun z =>
    poissonCellFieldValue ρ z x * poissonCellFieldValue ρ z y)
    ((poissonCellFieldValue_measurable_fixed ρ hρ x).mul
      (poissonCellFieldValue_measurable_fixed ρ hρ y))
    (fun z => by simp only [abs_mul, poissonCellFieldValue_abs, mul_one, le_refl])]
  have h_partitionFieldFiber_covariance n (x : X) (y : X) : (∫ z, partitionFieldFiberValue ρ z x * partitionFieldFiberValue ρ z y
      ∂partitionFieldFiberLaw μ n) = partitionSameProbability μ ρ x y ^ n := by
    have hm  :=
      (partitionFieldFiberValue_measurable_fixed ρ hρ n x).mul
        (partitionFieldFiberValue_measurable_fixed ρ hρ n y)
    have hi : Integrable (fun z =>
        partitionFieldFiberValue ρ z x * partitionFieldFiberValue ρ z y)
        (partitionFieldFiberLaw μ n) := Integrable.of_bound hm.aestronglyMeasurable 1
          (Filter.Eventually.of_forall (fun z => by
            simp only [Real.norm_eq_abs, abs_mul, partitionFieldFiberValue_abs, mul_one, le_refl]))
    rw [partitionFieldFiberLaw, integral_prod _ hi]
    simp only [partitionFieldFiberValue, cellSign_covariance]
    have he (h : Fin n → H) :
        (if partitionFieldPattern ρ h x = partitionFieldPattern ρ h y then 1 else 0) =
          ∏ i : Fin n, if ρ (h i) x = ρ (h i) y then (1 : ℝ) else 0 := by
      rw [Fintype.prod_boole]
      simp only [partitionFieldPattern, funext_iff]
      split_ifs <;> rfl
    simp_rw [he]
    rw [integral_fintype_prod_eq_pow (fun h => if ρ h x = ρ h y then (1 : ℝ) else 0)]
    simp only [Fintype.card_fin, partitionSameProbability]
  simp only [poissonCellFieldValue, h_partitionFieldFiber_covariance]
  exact (poisson_weighted_power_hasSum r (partitionSameProbability μ ρ x y)).tsum_eq
end
section
section
theorem even_cells_two_disjoint_pairs {I J : Type*} [DecidableEq I] [DecidableEq J]
    (s : Finset J) (p : J → I) (hs : 4 ≤ s.card)
    (h : ∀ i, Even ((s.filter (fun j => p j = i)).card)) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ∃ e ∈ s,
      b ≠ a ∧ c ≠ a ∧ c ≠ b ∧ e ≠ a ∧ e ≠ b ∧ e ≠ c ∧
        p b = p a ∧ p e = p c := by
  have h_even_cell_has_partner (s : Finset J) (p : J → I) (h : ∀ i, Even ((s.filter (fun j => p j = i)).card)) (a : J) (ha : a ∈ s) : ∃ b ∈ s, b ≠ a ∧ p b = p a := by
    let f := s.filter (fun j => p j = p a)
    have haf : a ∈ f := by simp [f, ha]
    have  := Finset.card_pos.mpr ⟨a, haf⟩
    have he : Even f.card := h (p a)
    obtain ⟨k, hk⟩ := he
    have : 2 ≤ f.card := by omega
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem haf]; omega)
    have hb' := Finset.mem_erase.mp hb
    exact ⟨b, (Finset.mem_filter.mp hb'.2).1, hb'.1,
      (Finset.mem_filter.mp hb'.2).2⟩
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  obtain ⟨b, hb, hab, hpab⟩ := h_even_cell_has_partner s p h a ha
  let t := (s.erase a).erase b
  have hbe : b ∈ s.erase a := by simp [hab, hb]
  have : 2 ≤ t.card := by
    simp only [t, Finset.card_erase_of_mem hbe, Finset.card_erase_of_mem ha]
    omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < t.card)
  have h_even_cells_erase_pair : ∀ i, Even (((s.erase a).erase b).filter (fun j => p j = i)).card := by
    intro i
    rw [Finset.filter_erase, Finset.filter_erase]
    by_cases hpa : p a = i
    · have hai : a ∈ s.filter (fun j => p j = i) := by simp [ha, hpa]
      have hbi : b ∈ s.filter (fun j => p j = i) := by simp [hb, hpab, hpa]
      have hbe : b ∈ (s.filter (fun j => p j = i)).erase a := by simp [hab, hbi]
      rw [Finset.card_erase_of_mem hbe, Finset.card_erase_of_mem hai]
      obtain ⟨k, hk⟩ := h i
      have : 2 ≤ (s.filter (fun j => p j = i)).card := by
        have hsub : ({a, b} : Finset J) ⊆ s.filter (fun j => p j = i) := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        have hh := Finset.card_le_card hsub
        simpa [Ne.symm hab] using hh
      exact ⟨k - 1, by omega⟩
    · have hai : a ∉ s.filter (fun j => p j = i) := by simp [hpa]
      have hbi : b ∉ s.filter (fun j => p j = i) := by simp [hpab, hpa]
      simp only [Finset.erase_eq_of_notMem hai, Finset.erase_eq_of_notMem hbi]
      exact h i
  obtain ⟨e, he, hec, hpec⟩ := h_even_cell_has_partner t p (h_even_cells_erase_pair) c hc
  have hct := Finset.mem_erase.mp hc
  have hct' := Finset.mem_erase.mp hct.2
  have het := Finset.mem_erase.mp he
  have het' := Finset.mem_erase.mp het.2
  exact ⟨a, ha, b, hb, c, hct'.2, e, het'.2, hab, hct'.1, hct.1,
    het'.1, het.1, hec, hpab, hpec⟩
variable {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
end
section
variable {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
def pairSameIndicator (ρ : H → X → Fin 2) (x y : X) (h : H) : ℝ :=
  if ρ h x = ρ h y then 1 else 0
def partitionBothProbability (μ : Measure H) (ρ : H → X → Fin 2) (a b c e : X) : ℝ :=
  ∫ h, pairSameIndicator ρ a b h * pairSameIndicator ρ c e h ∂μ
def partitionFiberBothIndicator (ρ : H → X → Fin 2) (n )
    (a b c e : X) (h : Fin n → H) : ℝ :=
  if partitionFieldPattern ρ h a = partitionFieldPattern ρ h b ∧
    partitionFieldPattern ρ h c = partitionFieldPattern ρ h e then 1 else 0
theorem partitionFiberBothIndicator_measurable (ρ : H → X → Fin 2)
    (hρ : Measurable (Function.uncurry ρ)) (n : ℕ) (a b c e : X) :
    Measurable (partitionFiberBothIndicator ρ n a b c e) := by
  apply Measurable.ite
  · apply MeasurableSet.inter
    · exact measurableSet_eq_fun
        ((partitionFieldPattern_measurable ρ hρ n).comp
          (measurable_id.prodMk measurable_const))
        ((partitionFieldPattern_measurable ρ hρ n).comp
          (measurable_id.prodMk measurable_const))
    · exact measurableSet_eq_fun
        ((partitionFieldPattern_measurable ρ hρ n).comp
          (measurable_id.prodMk measurable_const))
        ((partitionFieldPattern_measurable ρ hρ n).comp
          (measurable_id.prodMk measurable_const))
  · exact measurable_const
  · exact measurable_const
def poissonCellBothIndicator (ρ : H → X → Fin 2) (a b c e : X)
    (z : partitionFieldMark H) : ℝ := partitionFiberBothIndicator ρ z.1 a b c e z.2.1
end
abbrev CellMomentQuadruple (j : ℕ) := {q : Fin 4 → Fin j // Function.Injective q}
variable {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
def partitionFiberEvenIndicator (ρ : H → X → Fin 2) (n j )
    (U : Fin j → X) (h : Fin n → H) : ℝ :=
  if ∀ p,
    Even ((Finset.univ.filter (fun l => partitionFieldPattern ρ h (U l) = p)).card)
    then 1 else 0
theorem partitionFiberEvenIndicator_measurable (ρ : H → X → Fin 2)
    (hρ : Measurable (Function.uncurry ρ)) (n j : ℕ) (U : Fin j → X) :
    Measurable (partitionFiberEvenIndicator ρ n j U) := by
  let F : (Fin j → (Fin n → Fin 2)) → ℝ := fun p =>
    if ∀ c : Fin n → Fin 2, Even ((Finset.univ.filter (fun l => p l = c)).card)
      then 1 else 0
  have hF : Measurable F := measurable_of_finite _
  have hp : Measurable (fun h : Fin n → H => fun l => partitionFieldPattern ρ h (U l)) := by
    apply Measurable.of_eval
    intro l
    exact (partitionFieldPattern_measurable ρ hρ n).comp
      (measurable_id.prodMk measurable_const)
  exact hF.comp hp
def poissonCellEvenIndicator (ρ : H → X → Fin 2) (j ) (U : Fin j → X)
    (z : partitionFieldMark H) : ℝ := partitionFiberEvenIndicator ρ z.1 j U z.2.1
theorem poissonCellEvenIndicator_measurable (ρ : H → X → Fin 2)
    (hρ : Measurable (Function.uncurry ρ)) (j : ℕ) (U : Fin j → X) :
    Measurable (poissonCellEvenIndicator ρ j U) :=
  measurable_sigma_of_fibers _ (fun n =>
    (partitionFiberEvenIndicator_measurable ρ hρ n j U).comp measurable_fst)
theorem poissonCellField_product_moment_abs_le_two_pairs
    (μ ) [IsProbabilityMeasure μ] (r : ℝ≥0)
    (ρ : H → X → Fin 2) (hρ : Measurable (Function.uncurry ρ))
    (j : ℕ) (hj : 4 ≤ j) (U : Fin j → X) :
    |∫ z, ∏ l, poissonCellFieldValue ρ z (U l) ∂poissonCellFieldLaw μ r| ≤
      ∑ q : CellMomentQuadruple j, Real.exp (-↑r / 2 *
        ((1 - partitionSameProbability μ ρ (U (q.val 0)) (U (q.val 1))) +
          (1 - partitionSameProbability μ ρ (U (q.val 2)) (U (q.val 3))))) := by
  have h_pairSameIndicator_measurable (x : X) (y : X) : Measurable (pairSameIndicator ρ x y) := by
    apply Measurable.ite
    · exact measurableSet_eq_fun
        (hρ.comp (measurable_id.prodMk measurable_const))
        (hρ.comp (measurable_id.prodMk measurable_const))
    · exact measurable_const
    · exact measurable_const
  have h_partitionFieldFiber_product_moment (n : ℕ) (j : ℕ) (U : Fin j → X) : (∫ z, ∏ l, partitionFieldFiberValue ρ z (U l) ∂partitionFieldFiberLaw μ n) =
      ∫ h, if ∀ p : Fin n → Fin 2,
        Even ((Finset.univ.filter (fun l => partitionFieldPattern ρ h (U l) = p)).card)
        then ↑1 else 0 ∂Measure.pi (fun _ : Fin n => μ) := by
    have h_partitionFieldFiber_product_integrable : Integrable (fun z : partitionFieldFiber H n => ∏ l, partitionFieldFiberValue ρ z (U l))
        (partitionFieldFiberLaw μ n) := by
      apply Integrable.of_bound
        (Finset.measurable_prod _ (fun l _ =>
          partitionFieldFiberValue_measurable_fixed ρ hρ n (U l))).aestronglyMeasurable 1
      exact Filter.Eventually.of_forall (fun z => by
        simp only [Real.norm_eq_abs, Finset.abs_prod, partitionFieldFiberValue_abs,
          Finset.prod_const_one, le_refl])
    rw [partitionFieldFiberLaw, integral_prod _
      h_partitionFieldFiber_product_integrable]
    simp only [partitionFieldFiberValue, cellSign_product_moment]
  have h_pairSameIndicator_integrable (x : X) (y : X) : Integrable (pairSameIndicator ρ x y) μ := Integrable.of_bound (h_pairSameIndicator_measurable x y).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun h => by
      unfold pairSameIndicator
      split_ifs <;> norm_num))
  have h_poissonCellBothIndicator_measurable (a : X) (b : X) (c : X) (e : X) : Measurable (poissonCellBothIndicator ρ a b c e) := measurable_sigma_of_fibers _ (fun n =>
    (partitionFiberBothIndicator_measurable ρ hρ n a b c e).comp measurable_fst)
  have h_poissonCellField_product_moment_nonneg : 0 ≤ ∫ z, ∏ l, poissonCellFieldValue ρ z (U l) ∂poissonCellFieldLaw μ r := by
    rw [poissonCellField_integral_series μ r (fun z => ∏ l, poissonCellFieldValue ρ z (U l))
      (Finset.measurable_prod _ (fun l _ => poissonCellFieldValue_measurable_fixed ρ hρ (U l)))
      (fun z => by simp only [Finset.abs_prod, poissonCellFieldValue_abs,
        Finset.prod_const_one, le_refl])]
    apply tsum_nonneg
    intro n
    simp only [poissonCellFieldValue, h_partitionFieldFiber_product_moment]
    apply mul_nonneg (by positivity)
    apply integral_nonneg
    intro h
    dsimp only [Pi.zero_apply]
    split_ifs <;> norm_num
  rw [abs_of_nonneg h_poissonCellField_product_moment_nonneg]
  have h_poissonCellField_product_moment_le_two_pair_probabilities : (∫ z, ∏ l, poissonCellFieldValue ρ z (U l) ∂poissonCellFieldLaw μ r) ≤
      ∑ q : CellMomentQuadruple j, Real.exp (-↑r *
        (1 - partitionBothProbability μ ρ (U (q.val 0)) (U (q.val 1))
          (U (q.val 2)) (U (q.val 3)))) := by
    have h_poissonCellField_product_moment_eq_even : (∫ z, ∏ l, poissonCellFieldValue ρ z (U l) ∂poissonCellFieldLaw μ r) =
        ∫ z, poissonCellEvenIndicator ρ j U z ∂poissonCellFieldLaw μ r := by
      rw [poissonCellField_integral_series μ r _
        (Finset.measurable_prod _ (fun l _ => poissonCellFieldValue_measurable_fixed ρ hρ (U l)))
        (fun z => by simp only [Finset.abs_prod, poissonCellFieldValue_abs,
          Finset.prod_const_one, le_refl]),
        poissonCellField_integral_series μ r _ (poissonCellEvenIndicator_measurable ρ hρ j U)
          (fun z => by unfold poissonCellEvenIndicator partitionFiberEvenIndicator
                       split_ifs <;> norm_num)]
      apply tsum_congr
      intro n
      congr 1
      change (∫ z, ∏ l, partitionFieldFiberValue ρ z (U l) ∂partitionFieldFiberLaw μ n) = _
      rw [h_partitionFieldFiber_product_moment n j U]
      change (∫ h, partitionFiberEvenIndicator ρ n j U h ∂Measure.pi (fun _ : Fin n => μ)) =
        ∫ z, partitionFiberEvenIndicator ρ n j U z.1
          ∂(Measure.pi (fun _ : Fin n => μ)).prod (cellSignLaw (Fin n → Fin 2))
      rw [integral_fun_fst]
      simp
    rw [h_poissonCellField_product_moment_eq_even]
    have hi : Integrable (poissonCellEvenIndicator ρ j U) (poissonCellFieldLaw μ r) :=
      Integrable.of_bound (poissonCellEvenIndicator_measurable ρ hρ j U).aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun z => by
          unfold poissonCellEvenIndicator partitionFiberEvenIndicator
          split_ifs <;> norm_num))
    have hq (q : CellMomentQuadruple j) : Integrable (poissonCellBothIndicator ρ
        (U (q.val 0)) (U (q.val 1)) (U (q.val 2)) (U (q.val 3))) (poissonCellFieldLaw μ r) :=
      Integrable.of_bound (h_poissonCellBothIndicator_measurable _ _ _ _).aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun z => by
          unfold poissonCellBothIndicator partitionFiberBothIndicator
          split_ifs <;> norm_num))
    have h_partitionFiberEvenIndicator_le_pairs (n : ℕ) (h : Fin n → H) : partitionFiberEvenIndicator ρ n j U h ≤
        ∑ q : CellMomentQuadruple j, partitionFiberBothIndicator ρ n
          (U (q.val 0)) (U (q.val 1)) (U (q.val 2)) (U (q.val 3)) h := by
      unfold partitionFiberEvenIndicator
      split_ifs with heven
      · obtain ⟨a, _, b, _, c, _, e, _, hba, hca, hcb, hea, heb, hec, hab, hce⟩ :=
          even_cells_two_disjoint_pairs (Finset.univ : Finset (Fin j))
            (fun l => partitionFieldPattern ρ h (U l)) (by simpa using hj) heven
        let q : CellMomentQuadruple j := ⟨![a,b,c,e], (by intro i l hil; fin_cases i <;> fin_cases l <;> simp_all)⟩
        have hq : partitionFiberBothIndicator ρ n
            (U (q.val 0)) (U (q.val 1)) (U (q.val 2)) (U (q.val 3)) h = 1 := by
          simp only [q, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.cons_val_three, partitionFiberBothIndicator]
          simp [hab.symm, hce.symm]
        rw [← hq]
        exact Finset.single_le_sum (f := fun q =>
          partitionFiberBothIndicator ρ n (U (q.val 0)) (U (q.val 1))
            (U (q.val 2)) (U (q.val 3)) h) (fun q _ => by
          unfold partitionFiberBothIndicator
          split_ifs <;> norm_num) (Finset.mem_univ q)
      · apply Finset.sum_nonneg
        intro q _
        unfold partitionFiberBothIndicator
        split_ifs <;> norm_num
    calc
      _ ≤ ∫ z, ∑ q : CellMomentQuadruple j, poissonCellBothIndicator ρ
          (U (q.val 0)) (U (q.val 1)) (U (q.val 2)) (U (q.val 3)) z ∂poissonCellFieldLaw μ r :=
        integral_mono hi (integrable_finsetSum Finset.univ (fun q _ => hq q))
          (fun z => (h_partitionFiberEvenIndicator_le_pairs z.1 z.2.1))
      _ = _ := by
        rw [integral_finsetSum Finset.univ (fun q _ => hq q)]
        apply Finset.sum_congr rfl
        intro q _
        have h_poissonCellBothIndicator_integral (a : X) (b : X) (c : X) (e : X) : (∫ z, poissonCellBothIndicator ρ a b c e z ∂poissonCellFieldLaw μ r) =
            Real.exp (-↑r * (1 - partitionBothProbability μ ρ a b c e)) := by
          rw [poissonCellField_integral_series μ r _
            (h_poissonCellBothIndicator_measurable a b c e)
            (fun z => by unfold poissonCellBothIndicator partitionFiberBothIndicator
                         split_ifs <;> norm_num)]
          have hf n : (∫ z : partitionFieldFiber H n,
              poissonCellBothIndicator ρ a b c e ⟨n, z⟩ ∂partitionFieldFiberLaw μ n) =
              partitionBothProbability μ ρ a b c e ^ n := by
            change (∫ z : (Fin n → H) × ((Fin n → Fin 2) → Fin 2),
              partitionFiberBothIndicator ρ n a b c e z.1
              ∂(Measure.pi (fun _ => μ)).prod (cellSignLaw (Fin n → Fin 2))) = _
            rw [integral_fun_fst]
            have h_partitionFiberBothIndicator_integral : (∫ h, partitionFiberBothIndicator ρ n a b c e h
                ∂Measure.pi (fun _ : Fin n => μ)) = partitionBothProbability μ ρ a b c e ^ n := by
              have he (h : Fin n → H) : partitionFiberBothIndicator ρ n a b c e h =
                  ∏ i : Fin n, pairSameIndicator ρ a b (h i) * pairSameIndicator ρ c e (h i) := by
                have hh (z : H) : pairSameIndicator ρ a b z * pairSameIndicator ρ c e z =
                    if ρ z a = ρ z b ∧ ρ z c = ρ z e then 1 else 0 := by
                  unfold pairSameIndicator
                  split_ifs <;> norm_num <;> aesop
                simp_rw [hh]
                unfold partitionFiberBothIndicator
                rw [Fintype.prod_boole]
                simp only [partitionFieldPattern, funext_iff, forall_and]
              simp_rw [he]
              rw [integral_fintype_prod_eq_pow
                (fun h => pairSameIndicator ρ a b h * pairSameIndicator ρ c e h)]
              simp only [partitionBothProbability, Fintype.card_fin]
            simpa using h_partitionFiberBothIndicator_integral
          simp_rw [hf]
          exact (poisson_weighted_power_hasSum r _).tsum_eq
        exact h_poissonCellBothIndicator_integral _ _ _ _
  apply h_poissonCellField_product_moment_le_two_pair_probabilities.trans
  apply Finset.sum_le_sum
  intro q _
  apply Real.exp_le_exp.mpr
  have h_partition_union_separation_ge_half (a : X) (b : X) (c : X) (e : X) : ((1 - partitionSameProbability μ ρ a b) +
      1 - partitionSameProbability μ ρ c e) / 2 ≤
        1 - partitionBothProbability μ ρ a b c e := by
    have hp : Integrable (fun h => pairSameIndicator ρ a b h * pairSameIndicator ρ c e h) μ :=
      Integrable.of_bound
        ((h_pairSameIndicator_measurable a b).mul
          (h_pairSameIndicator_measurable c e)).aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun h => by
          unfold pairSameIndicator
          split_ifs <;> norm_num))
    have hs := ((h_pairSameIndicator_integrable a b).add
      (h_pairSameIndicator_integrable c e)).div_const 2
    have h := integral_mono hp hs (fun h => show
        pairSameIndicator ρ a b h * pairSameIndicator ρ c e h ≤
          (pairSameIndicator ρ a b h + pairSameIndicator ρ c e h) / 2 by
        unfold pairSameIndicator
        split_ifs <;> norm_num)
    rw [integral_div] at h
    change (∫ h, pairSameIndicator ρ a b h * pairSameIndicator ρ c e h ∂μ) ≤
      (∫ h, pairSameIndicator ρ a b h + pairSameIndicator ρ c e h ∂μ) / 2 at h
    rw [integral_add (h_pairSameIndicator_integrable a b)
      (h_pairSameIndicator_integrable c e)] at h
    change partitionBothProbability μ ρ a b c e ≤
      (partitionSameProbability μ ρ a b + partitionSameProbability μ ρ c e) / 2 at h
    linarith
  nlinarith only [h_partition_union_separation_ge_half (U (q.val 0)) (U (q.val 1)) (U (q.val 2)) (U (q.val 3)), r.coe_nonneg]
end
def hyperplaneRadius  (Z : Covariate d) : ℝ := ∑ r, |Z r|
def hyperplaneCube (d ) : Set (Covariate d) := {u | ∀ r, |u r| ≤ 1}
def hyperplaneSlab (d ) : Set (Covariate d × ℝ) :=
  {h | |h.2| ≤ hyperplaneRadius h.1}
def gaussianHyperplaneIntensity (d ) : Measure (Covariate d × ℝ) :=
  ((standardGaussianPi d).prod volume).restrict (hyperplaneSlab d)
def hyperplaneHalfspace  (h : Covariate d × ℝ) (u : Covariate d) : Fin 2 :=
  if gaussianPhase u h.1 ≤ h.2 then 0 else 1
theorem hyperplaneRadius_nonneg  (Z : Covariate d) : 0 ≤ hyperplaneRadius Z :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)
theorem hyperplaneRadius_continuous  : Continuous (hyperplaneRadius (d := d)) := by
  unfold hyperplaneRadius
  fun_prop
theorem hyperplaneHalfspace_measurable  :
    Measurable (Function.uncurry (hyperplaneHalfspace (d := d))) := by
  exact Measurable.ite (measurableSet_le (by unfold gaussianPhase; fun_prop) measurable_fst.snd) measurable_const measurable_const
theorem hyperplane_phase_bound  (Z u ) (hu : u ∈ hyperplaneCube d) :
    |gaussianPhase u Z| ≤ hyperplaneRadius Z := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro r _
  rw [abs_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hu r) (abs_nonneg (Z r))
def hyperplaneSeparationSet  (u v : Covariate d) : Set (Covariate d × ℝ) :=
  {h | hyperplaneHalfspace h u ≠ hyperplaneHalfspace h v}
theorem hyperplaneSeparationSet_measurable  (u v : Covariate d) :
    MeasurableSet (hyperplaneSeparationSet u v) := by
  exact (measurableSet_eq_fun
    (hyperplaneHalfspace_measurable.comp (measurable_id.prodMk measurable_const))
    (hyperplaneHalfspace_measurable.comp (measurable_id.prodMk measurable_const))).compl
theorem hyperplane_separation_slice  (Z u v : Covariate d) :
    (fun b : ℝ => (Z, b)) ⁻¹' hyperplaneSeparationSet u v =
      Ico (min (gaussianPhase u Z) (gaussianPhase v Z))
        (max (gaussianPhase u Z) (gaussianPhase v Z)) := by
  ext b
  unfold hyperplaneSeparationSet hyperplaneHalfspace
  simp only [mem_preimage, mem_setOf_eq, mem_Ico]
  rcases le_total (gaussianPhase u Z) (gaussianPhase v Z) with huv | hvu
  · rw [min_eq_left huv, max_eq_right huv]
    split_ifs <;> norm_num <;> grind
  · rw [min_eq_right hvu, max_eq_left hvu]
    split_ifs <;> norm_num <;> grind
theorem hyperplane_separation_slice_volume  (Z u v : Covariate d) :
    volume ((fun b : ℝ => (Z, b)) ⁻¹' hyperplaneSeparationSet u v) =
      ENNReal.ofReal |gaussianPhase u Z - gaussianPhase v Z| := by
  rw [hyperplane_separation_slice, Real.volume_Ico, max_sub_min_eq_abs, abs_sub_comm]
theorem gaussianHyperplaneIntensity_univ (d ) :
    gaussianHyperplaneIntensity d univ =
      ∫⁻ Z, ENNReal.ofReal (2 * hyperplaneRadius Z) ∂standardGaussianPi d := by
  have h_hyperplane_slab_slice (Z : Covariate d) : (fun b => (Z, b)) ⁻¹' hyperplaneSlab d =
      Icc (-hyperplaneRadius Z) (hyperplaneRadius Z) := by
    ext b
    simp only [hyperplaneSlab, mem_preimage, mem_setOf_eq, mem_Icc, abs_le]
  have h_hyperplaneSlab_measurable : MeasurableSet (hyperplaneSlab d) := measurableSet_le (measurable_snd.abs) (hyperplaneRadius_continuous.measurable.comp measurable_fst)
  rw [gaussianHyperplaneIntensity, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Measure.prod_apply h_hyperplaneSlab_measurable]
  simp_rw [h_hyperplane_slab_slice, Real.volume_Icc]
  congr 1
  ext Z
  congr 1
  ring
theorem hyperplane_coordinate_integrable  (r ) :
    Integrable (fun Z => Z r) (standardGaussianPi d) := by
  exact integrable_comp_eval (μ := fun _ => standardGaussianLine) (i := r) (f := id)
    ((memLp_id_gaussianReal (μ := 0) (v := 1) (1 : ℝ≥0)).integrable (by norm_num))
theorem hyperplaneRadius_integrable (d ) :
    Integrable (hyperplaneRadius (d := d)) (standardGaussianPi d) := integrable_finsetSum _ (fun r _ => (hyperplane_coordinate_integrable r).abs)
def hyperplaneNormalizingConstant (d : ℕ) : ℝ :=
  ∫ Z, 2 * hyperplaneRadius Z ∂standardGaussianPi d
theorem gaussianHyperplaneIntensity_univ_ofReal (d ) :
    gaussianHyperplaneIntensity d univ = ENNReal.ofReal (hyperplaneNormalizingConstant d) := by
  rw [gaussianHyperplaneIntensity_univ]
  exact (ofReal_integral_eq_lintegral_ofReal ((hyperplaneRadius_integrable d).const_mul 2)
    (Filter.Eventually.of_forall (fun Z => mul_nonneg (by norm_num) (hyperplaneRadius_nonneg Z)))).symm
theorem hyperplanePhase_integrable  (u ) :
    Integrable (gaussianPhase u) (standardGaussianPi d) := integrable_finsetSum _ (fun r _ => (hyperplane_coordinate_integrable r).const_mul (u r))
def gaussianAbsoluteMean : ℝ := ∫ z : ℝ, |z| ∂standardGaussianLine
theorem standardGaussianLine_abs_integrable :
    Integrable (fun z => |z|) standardGaussianLine := by
  simpa only [Real.norm_eq_abs, id_eq] using
    (IsGaussian.integrable_id (μ := standardGaussianLine)).norm
theorem gaussianAbsoluteMean_pos : 0 < gaussianAbsoluteMean := by
  by_contra h
  have hz  := le_antisymm (not_lt.mp h) (integral_nonneg (fun _ => abs_nonneg _))
  have hid : id =ᵐ[standardGaussianLine] (fun _ => 0) := by
    filter_upwards [(integral_eq_zero_iff_of_nonneg (fun z => abs_nonneg z) standardGaussianLine_abs_integrable).mp hz] with z hz
    exact abs_eq_zero.mp hz
  have hv := variance_congr hid
  rw [variance_id_gaussianReal] at hv
  change 1 = Var[(0 : ℝ → ℝ); standardGaussianLine] at hv
  rw [variance_zero] at hv
  exact one_ne_zero hv
theorem gaussianPhase_eq_inner  (v Z : Covariate d) :
    gaussianPhase v Z = inner ℝ (WithLp.toLp 2 v) (WithLp.toLp 2 Z) := by
  simp only [gaussianPhase, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]
theorem gaussianPhase_map_eq_scaled_gaussian  (v ) :
    (standardGaussianPi d).map (gaussianPhase v) =
      standardGaussianLine.map (fun z : ℝ => euclideanNorm v * z) := by
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin d)) := innerSL ℝ (WithLp.toLp 2 v)
  have hfun : gaussianPhase v = L ∘ (WithLp.toLp 2) := by
    funext Z
    exact gaussianPhase_eq_inner v Z
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop),
    map_pi_eq_stdGaussian, IsGaussian.map_eq_gaussianReal L,
    integral_strongDual_stdGaussian, variance_dual_stdGaussian, gaussianReal_map_const_mul]
  simp only [mul_zero, mul_one]
  congr 1
  apply NNReal.coe_injective
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  have h_euclideanNorm_eq_toLp_norm : euclideanNorm v = ‖WithLp.toLp 2 v‖ := by
    simp only [euclideanNorm, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]
  simp only [L, innerSL_apply_norm, ← h_euclideanNorm_eq_toLp_norm]
  rfl
theorem gaussianPhase_abs_integral  (v ) :
    (∫ Z, |gaussianPhase v Z| ∂standardGaussianPi d) =
      gaussianAbsoluteMean * euclideanNorm v := by
  have hphase : Measurable (gaussianPhase v) := by unfold gaussianPhase; fun_prop
  have habs : AEStronglyMeasurable (fun z => |z|)
      ((standardGaussianPi d).map (gaussianPhase v)) := (by fun_prop : Measurable (fun z => |z|)).aestronglyMeasurable
  rw [← integral_map hphase.aemeasurable habs, gaussianPhase_map_eq_scaled_gaussian v,
    integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, abs_of_nonneg (show 0 ≤ euclideanNorm v by unfold euclideanNorm; positivity)]
  rw [integral_const_mul]
  exact mul_comm _ _
theorem hyperplaneNormalizingConstant_actual (d ) :
    hyperplaneNormalizingConstant d = 2 * d * gaussianAbsoluteMean :=
  have h_hyperplaneNormalizingConstant_eq : hyperplaneNormalizingConstant d =
      2 * d * (∫ z : ℝ, |z| ∂standardGaussianLine) := by
    rw [hyperplaneNormalizingConstant, integral_const_mul]
    unfold hyperplaneRadius
    rw [integral_finsetSum _ (fun r _ => (hyperplane_coordinate_integrable r).abs)]
    have hi (r : Fin d) : (∫ Z : Covariate d, |Z r| ∂standardGaussianPi d) =
        ∫ z : ℝ, |z| ∂standardGaussianLine := by
      exact integral_comp_eval (μ := fun _ => standardGaussianLine)
        (f := fun z => |z|) (i := r) (by fun_prop)
    simp_rw [hi]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  h_hyperplaneNormalizingConstant_eq
theorem hyperplaneNormalizingConstant_pos (d ) [NeZero d] :
    0 < hyperplaneNormalizingConstant d := by
  rw [hyperplaneNormalizingConstant_actual]
  exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr (NeZero.pos d))) gaussianAbsoluteMean_pos
def gaussianHyperplaneLaw (d ) : Measure (Covariate d × ℝ) :=
  (ENNReal.ofReal (hyperplaneNormalizingConstant d))⁻¹ • gaussianHyperplaneIntensity d
instance gaussianHyperplaneLaw_probability (d : ℕ) [NeZero d] :
    IsProbabilityMeasure (gaussianHyperplaneLaw d) := by
  constructor
  rw [gaussianHyperplaneLaw, Measure.smul_apply, smul_eq_mul,
    gaussianHyperplaneIntensity_univ_ofReal]
  exact ENNReal.inv_mul_cancel (by simp [hyperplaneNormalizingConstant_pos d])
    ENNReal.ofReal_ne_top
theorem gaussianHyperplaneLaw_separation_real (d ) [NeZero d] (u v )
    (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d) :
    (gaussianHyperplaneLaw d).real (hyperplaneSeparationSet u v) =
      euclideanNorm (fun r => u r - v r) / (2 * d) := by
  rw [gaussianHyperplaneLaw, measureReal_ennreal_smul_apply, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (hyperplaneNormalizingConstant_pos d).le]
  have h_gaussianHyperplaneIntensity_separation_ofReal : gaussianHyperplaneIntensity d (hyperplaneSeparationSet u v) =
      ENNReal.ofReal (∫ Z, |gaussianPhase u Z - gaussianPhase v Z| ∂standardGaussianPi d) := by
    have h_gaussianHyperplaneIntensity_separation : gaussianHyperplaneIntensity d (hyperplaneSeparationSet u v) =
        ∫⁻ Z, ENNReal.ofReal |gaussianPhase u Z - gaussianPhase v Z| ∂standardGaussianPi d := by
      have h_hyperplane_separation_subset_slab : hyperplaneSeparationSet u v ⊆ hyperplaneSlab d := by
        intro h hh
        have hs  := (Set.ext_iff.mp (hyperplane_separation_slice h.1 u v) h.2).mp hh
        have hu' := abs_le.mp (hyperplane_phase_bound h.1 u hu)
        have hv' := abs_le.mp (hyperplane_phase_bound h.1 v hv)
        exact abs_le.mpr ⟨(le_min hu'.1 hv'.1).trans hs.1,
          hs.2.le.trans (max_le hu'.2 hv'.2)⟩
      rw [gaussianHyperplaneIntensity, Measure.restrict_apply
        (hyperplaneSeparationSet_measurable u v),
        inter_eq_left.mpr h_hyperplane_separation_subset_slab,
        Measure.prod_apply (hyperplaneSeparationSet_measurable u v)]
      simp_rw [hyperplane_separation_slice_volume]
    rw [h_gaussianHyperplaneIntensity_separation]
    exact (ofReal_integral_eq_lintegral_ofReal
      ((hyperplanePhase_integrable u).sub (hyperplanePhase_integrable v)).abs
      (Filter.Eventually.of_forall (fun _ => abs_nonneg _))).symm
  rw [measureReal_def, h_gaussianHyperplaneIntensity_separation_ofReal]
  have h_gaussianPhase_sub (Z : Covariate d) : gaussianPhase u Z - gaussianPhase v Z = gaussianPhase (fun r => u r - v r) Z := by
    simp only [gaussianPhase, sub_mul, Finset.sum_sub_distrib]
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun _ => abs_nonneg _))]
  simp_rw [h_gaussianPhase_sub]
  rw [gaussianPhase_abs_integral, hyperplaneNormalizingConstant_actual]
  have : d ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have := gaussianAbsoluteMean_pos.ne'
  field_simp
theorem gaussianHyperplaneLaw_same_complement (d ) [NeZero d] (u v ) :
    1 - partitionSameProbability (gaussianHyperplaneLaw d) hyperplaneHalfspace u v =
      (gaussianHyperplaneLaw d).real (hyperplaneSeparationSet u v) := by
  let s : Set (Covariate d × ℝ) := {h | hyperplaneHalfspace h u = hyperplaneHalfspace h v}
  have hs : MeasurableSet s := (hyperplaneSeparationSet_measurable u v).of_compl
  have he : partitionSameProbability (gaussianHyperplaneLaw d) hyperplaneHalfspace u v =
      (gaussianHyperplaneLaw d).real s := by
    simpa only [partitionSameProbability, s, Set.indicator, Pi.one_apply, Set.mem_setOf_eq] using
      (integral_indicator_one (μ := gaussianHyperplaneLaw d) hs)
  rw [he]
  change 1 - (gaussianHyperplaneLaw d).real s = (gaussianHyperplaneLaw d).real sᶜ
  rw [measureReal_compl hs]
  simp
def boundedHyperplaneFieldLaw (d ) (T : ℝ) : Measure (partitionFieldMark (Covariate d × ℝ)) :=
  poissonCellFieldLaw (gaussianHyperplaneLaw d) (Real.toNNReal (2 * d * T))
def boundedHyperplaneFieldValue  (z : partitionFieldMark (Covariate d × ℝ))
    (u : Covariate d) : ℝ := poissonCellFieldValue hyperplaneHalfspace z u
instance boundedHyperplaneFieldLaw_probability (d : ℕ) [NeZero d] (T : ℝ) :
    IsProbabilityMeasure (boundedHyperplaneFieldLaw d T) := by
  unfold boundedHyperplaneFieldLaw
  infer_instance
theorem boundedHyperplaneFieldLaw_measurable (d ) :
    Measurable (boundedHyperplaneFieldLaw d) := by
  exact (poissonCellFieldLaw_measurable (gaussianHyperplaneLaw d)).comp
    (measurable_real_toNNReal.comp (measurable_const.mul measurable_id))
theorem boundedHyperplaneFieldValue_measurable (d ) :
    Measurable (fun z : partitionFieldMark (Covariate d × ℝ) × Covariate d =>
      boundedHyperplaneFieldValue z.1 z.2) :=
  poissonCellFieldValue_measurable hyperplaneHalfspace hyperplaneHalfspace_measurable
theorem boundedHyperplaneFieldValue_abs 
    (z : partitionFieldMark (Covariate d × ℝ)) (u : Covariate d) :
    |boundedHyperplaneFieldValue z u| = 1 := poissonCellFieldValue_abs _ _ _
end
variable {U : Type*}
def fineModulationNode (i : Fin 3) : ℝ := if i = 0 then -1 else if i = 1 then 0 else 1
def fineModulationWeight (i : Fin 3) : ℝ := if i = 1 then -1 else 1 / 2
theorem fineModulation_eval (f : ℝ → ℝ) :
    (∑ i : Fin 3, fineModulationWeight i * f (fineModulationNode i)) =
      f (-1) / 2 - f 0 + f 1 / 2 := by
  simp [Fin.sum_univ_succ, fineModulationWeight, fineModulationNode]
  ring
theorem fineModulationNode_bound (i ) : |fineModulationNode i| ≤ 1 := by
  fin_cases i <;> norm_num [fineModulationNode]
theorem fineModulationWeight_variation : (∑ i : Fin 3, |fineModulationWeight i|) = 2 := by
  norm_num [Fin.sum_univ_succ, fineModulationWeight]
theorem fineModulation_moment_zero :
    (∑ i : Fin 3, fineModulationWeight i * fineModulationNode i ^ 0) = 0 := by
  rw [fineModulation_eval (fun z => z ^ 0)]
  norm_num
theorem fineModulation_moment (n : ℕ) :
    (∑ i : Fin 3, fineModulationWeight i * fineModulationNode i ^ n) =
      if n = 0 then 0 else if Even n then 1 else 0 := by
  by_cases hn0 : n = 0
  · subst n; simp only [ite_true]; exact fineModulation_moment_zero
  · rw [ite_eq_right hn0]
    rcases Nat.even_or_odd n with hn | hn
    · rw [ite_eq_left hn]; exact (by rw [fineModulation_eval (fun z => z ^ n)]; simp [hn.neg_one_pow, zero_pow hn0]; norm_num)
    have h_fineModulation_moment_odd : (∑ i : Fin 3, fineModulationWeight i * fineModulationNode i ^ n) = 0 := by
      rw [fineModulation_eval (fun z => z ^ n)]
      have hn0 : n ≠ 0 := by intro h; subst n; exact Nat.not_odd_zero hn
      simp [hn.neg_one_pow, zero_pow hn0]
      norm_num
    · rw [ite_eq_right (Nat.not_even_iff_odd.mpr hn)]; exact h_fineModulation_moment_odd
abbrev FinePairDensityIndex (M : ℕ) := Fin (M + 3) × Fin 3
def finePairDensityPrefactor (a b : ℝ) : ℝ := b ^ 2 / densityMargin a b 0 ^ 2
def finePairDensityAtom (a b : ℝ) (M ) (i : FinePairDensityIndex M) : ℝ × ℝ :=
  (exteriorNode a b (M + 2) i.1, fineModulationNode i.2)
def finePairDensityWeight (a b : ℝ) (M ) (i : FinePairDensityIndex M) : ℝ :=
  finePairDensityPrefactor a b * exteriorWeight a b (M + 2) i.1 * fineModulationWeight i.2
def finePairDensitySignedRule (a b : ℝ) (M : ℕ) : SignedMeasure (ℝ × ℝ) :=
  atomicSignedRule (finePairDensityAtom a b M) (finePairDensityWeight a b M)
theorem finePairDensityWeight_variation (a b ) (ha : 0 < a) (hab : a < b) (M ) :
    (∑ i : FinePairDensityIndex M, |finePairDensityWeight a b M i|) =
      2 * |finePairDensityPrefactor a b| *
        Real.cosh ((M + 2 : ℕ) * exteriorTau ((a + b) / (b - a))) := by
  simp only [finePairDensityWeight, abs_mul, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, fineModulationWeight_variation]
  rw [← Finset.sum_mul, ← Finset.mul_sum, exterior_rule_variation a b ha hab (M + 2) (by omega)]
  ring
def finePairDensityReset  (a b z eps : ℝ) (p ψ : U → ℝ) (u : U) : ℝ :=
  z + densityMargin a b z / b * p u * eps * ψ u
theorem finePairDensityReset_mem_interval  (a b ) (ha : 0 < a) (hab : a < b)
    (z eps ) (hz : z ∈ Icc a b) (heps : |eps| ≤ 1)
    (p ψ : U → ℝ) (u : U) (hp : p u ∈ Icc a b) (hψ : |ψ u| ≤ 1) :
    finePairDensityReset a b z eps p ψ u ∈ Icc a b := by
  have hh := localDensityReset_mem_interval a b ha hab 1 (by omega) z hz (fun _ => eps)
    (fun _ => heps) p (fun u _ => ψ u) u hp (fun _ => hψ)
  simpa [localDensityReset, finePairDensityReset, mul_comm, mul_left_comm, mul_assoc] using hh
theorem fineModulation_affine_zero (z c : ℝ) :
    (∑ i : Fin 3, fineModulationWeight i * (z + c * fineModulationNode i)) = 0 := by
  rw [fineModulation_eval (fun eps => z + c * eps)]
  ring
theorem fineModulation_quadratic (z c c' : ℝ) :
    (∑ i : Fin 3, fineModulationWeight i *
      ((z + c * fineModulationNode i) * (z + c' * fineModulationNode i))) = c * c' := by
  rw [fineModulation_eval (fun eps => (z + c * eps) * (z + c' * eps))]
  ring
theorem fineModulation_product {ι : Type*} [DecidableEq ι] (S : Finset ι) (z : ℝ) (c : ι → ℝ) :
    (∑ h : Fin 3, fineModulationWeight h * ∏ i ∈ S, (z + c i * fineModulationNode h)) =
      ∑ U ∈ S.powerset, z ^ (S.card - U.card) * (∏ i ∈ U, c i) *
        (if U.card = 0 then 0 else if Even U.card then 1 else 0) := by
  simp_rw [add_comm z, Finset.prod_add, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  simp only [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hU)]
  have he (h : Fin 3) : fineModulationWeight h *
      ((∏ i ∈ U, c i) * fineModulationNode h ^ U.card * z ^ (S.card - U.card)) =
      z ^ (S.card - U.card) * (∏ i ∈ U, c i) *
        (fineModulationWeight h * fineModulationNode h ^ U.card) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum, fineModulation_moment]
def finePairCountCoefficient (a b : ℝ) (M k j : ℕ) : ℝ :=
  finePairDensityPrefactor a b * ∑ h : Fin (M + 3), exteriorWeight a b (M + 2) h *
    (exteriorNode a b (M + 2) h ^ (k - j) * (densityMargin a b (exteriorNode a b (M + 2) h) / b) ^ j)
theorem finePairDensitySignedRule_integral (a b : ℝ) (M : ℕ) (f : ℝ → ℝ → ℝ) :
    (∫ᵛ e, f e.1 e.2 ∂<•finePairDensitySignedRule a b M) =
      finePairDensityPrefactor a b * ∑ j : Fin (M + 3), exteriorWeight a b (M + 2) j *
        ∑ i : Fin 3, fineModulationWeight i * f (exteriorNode a b (M + 2) j) (fineModulationNode i) := by
  rw [finePairDensitySignedRule, atomicSignedRule_integral]
  simp only [finePairDensityAtom, finePairDensityWeight, Fintype.sum_prod_type]
  simp_rw [mul_assoc, ← Finset.mul_sum]
theorem finePairDensitySignedRule_product_expansion  [DecidableEq U]
    (a b M) (S : Finset U) (p ψ : U → ℝ) :
    (∫ᵛ e, ∏ u ∈ S, finePairDensityReset a b e.1 e.2 p ψ u
      ∂<•finePairDensitySignedRule a b M) =
      ∑ W ∈ S.powerset, finePairCountCoefficient a b M S.card W.card * (∏ u ∈ W, p u * ψ u) *
        (if W.card = 0 then 0 else if Even W.card then 1 else 0) := by
  rw [finePairDensitySignedRule_integral a b M (fun z eps => ∏ u ∈ S, finePairDensityReset a b z eps p ψ u)]
  have he (z eps : ℝ) (u : U) : finePairDensityReset a b z eps p ψ u =
      z + (densityMargin a b z / b * (p u * ψ u)) * eps := by
    unfold finePairDensityReset
    ring
  have hprod (z : ℝ) (W : Finset U) :
      (∏ u ∈ W, densityMargin a b z / b * (p u * ψ u)) =
      (densityMargin a b z / b) ^ W.card * (∏ u ∈ W, p u * ψ u) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp_rw [he, fineModulation_product, hprod]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro W hW
  unfold finePairCountCoefficient
  have hterm (h : Fin (M + 3)) : finePairDensityPrefactor a b *
      (exteriorWeight a b (M + 2) h *
       (exteriorNode a b (M + 2) h ^ (S.card - W.card) *
        ((densityMargin a b (exteriorNode a b (M + 2) h) / b) ^ W.card * ∏ u ∈ W, p u * ψ u) *
        (if W.card = 0 then 0 else if Even W.card then 1 else 0))) =
      finePairDensityPrefactor a b *
        (exteriorWeight a b (M + 2) h * (exteriorNode a b (M + 2) h ^ (S.card - W.card) *
          (densityMargin a b (exteriorNode a b (M + 2) h) / b) ^ W.card)) *
        ((∏ u ∈ W, p u * ψ u) * (if W.card = 0 then 0 else if Even W.card then 1 else 0)) := by ring
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring
section Field
variable {Z : Type*} [MeasurableSpace Z]
def finePairFieldReset  (a b : ℝ) (M ) (p : U → ℝ) (ψ : Z → U → ℝ)
    (e : Z × FinePairDensityIndex M) (u : U) : ℝ :=
  finePairDensityReset a b (finePairDensityAtom a b M e.2).1
    (finePairDensityAtom a b M e.2).2 p (ψ e.1) u
theorem finePairFieldReset_abs_le  (a b ) (ha : 0 < a) (hab : a < b)
    (M : ℕ) (p : U → ℝ) (hp : ∀ u, p u ∈ Icc a b) (ψ : Z → U → ℝ)
    (hψ : ∀ ζ u, |ψ ζ u| ≤ 1) (e : Z × FinePairDensityIndex M) (u : U) :
    |finePairFieldReset a b M p ψ e u| ≤ b := by
  have h_finePairFieldReset_mem_interval : finePairFieldReset a b M p ψ e u ∈ Icc a b := finePairDensityReset_mem_interval a b ha hab _ _
    (exteriorNode_mem a b hab.le (M + 2) e.2.1) (fineModulationNode_bound e.2.2)
    p (ψ e.1) u (hp u) (hψ e.1 u)
  have hh := h_finePairFieldReset_mem_interval
  rw [abs_of_nonneg (ha.le.trans hh.1)]
  exact hh.2
end Field
abbrev FinePairPacketIndex (ι : Type*) (M q : ℕ) := FinePairDensityIndex M × HighResponseMarkIndex ι q
section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
def finePairPacketWeight (a b : ℝ) (M q ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  finePairDensityWeight a b M e.2.1 * highResponseMarkWeight C q (A e.1) e.2.2
theorem finePairPacketWeight_slice_measurable (a b M q C)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (h ) : Measurable (fun ζ => finePairPacketWeight a b M q C A (ζ, h)) := by
  dsimp [finePairPacketWeight, highResponseMarkWeight, covarianceWeight]
  fun_prop
theorem finePairPacketWeight_measurable (a b M q C)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) :
    Measurable (finePairPacketWeight a b M q C A) :=
  measurable_from_prod_countable_left (finePairPacketWeight_slice_measurable a b M q C A hA)
theorem finePairPacketWeight_integrable (σ : Measure Z) [IsFiniteMeasure σ]
    (a b M q C) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ) :
    Integrable (finePairPacketWeight a b M q C A) (σ.prod Measure.count) :=
  have h_finePairPacketWeight_slice_integrable (h : FinePairPacketIndex ι M q) : Integrable (fun ζ => finePairPacketWeight a b M q C A (ζ, h)) σ := by
    exact (((((separatedMatrix_entry_integrable σ A hA hcost h.2.1.1 h.2.1.2).const_mul
      (C ^ 2 / 2)).mul_const (fairSign h.2.2.1.1)).mul_const (fairSign h.2.2.1.2)).const_mul
        (responseWeight q h.2.2.2)).const_mul (finePairDensityWeight a b M h.1)
  joint_finite_integrable σ _ (finePairPacketWeight_slice_measurable a b M q C A hA)
    h_finePairPacketWeight_slice_integrable
def finePairPacketSignedMeasure (σ : Measure Z) (a b : ℝ) (M q ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : SignedMeasure (Z × FinePairPacketIndex ι M q) :=
  (σ.prod Measure.count).withDensityᵥ (finePairPacketWeight a b M q C A)
theorem finePairPacketSignedMeasure_totalVariation (σ ) [IsFiniteMeasure σ]
    (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ) :
    ((finePairPacketSignedMeasure σ a b M q C A).variation univ).toReal =
      (∑ h : FinePairDensityIndex M, |finePairDensityWeight a b M h|) *
        (∑ h : Fin (2 * q + 2), |responseWeight q h|) * 2 * C ^ 2 *
          (∫ ζ, separatedMatrixCost A ζ ∂σ) := by
  have hw := finePairPacketWeight_integrable σ a b M q C A hA hcost
  rw [finePairPacketSignedMeasure, Measure.variation_withDensityᵥ hw,
    withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← integral_norm_eq_lintegral_enorm hw.aestronglyMeasurable, integral_prod _ hw.norm]
  have h_finePairPacketWeight_variation (ζ : Z) : (∑ h : FinePairPacketIndex ι M q, |finePairPacketWeight a b M q C A (ζ, h)|) =
      (∑ h : FinePairDensityIndex M, |finePairDensityWeight a b M h|) *
        (∑ h : Fin (2 * q + 2), |responseWeight q h|) * 2 * C ^ 2 * separatedMatrixCost A ζ := by
    rw [Fintype.sum_prod_type]
    simp only [finePairPacketWeight, abs_mul]
    simp_rw [← Finset.mul_sum, highResponseMark_variation]
    rw [← Finset.sum_mul]
    unfold separatedMatrixCost
    ring
  simp only [integral_count, Real.norm_eq_abs, h_finePairPacketWeight_variation]
  rw [integral_const_mul]
def finePairPacketObservable (a b : ℝ) (M q ) (C : ℝ) (c : ι → ℝ)
    (G : Z → ℝ → ℝ → ℝ) (Φ : (ι → ℝ) → ℝ)
    (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  G e.1 (finePairDensityAtom a b M e.2.1).1 (finePairDensityAtom a b M e.2.1).2 *
    Φ (coefficientReset c (highResponseMarkAtom C q e.2.2).2 (highResponseMarkAtom C q e.2.2).1)
theorem finePairPacketObservable_finite_action (a b M q C)
    (A : Z → ι → ι → ℝ) (c : ι → ℝ) (G : Z → ℝ → ℝ → ℝ) (Φ : (ι → ℝ) → ℝ) (ζ : Z) :
    (∑ h : FinePairPacketIndex ι M q, finePairPacketWeight a b M q C A (ζ, h) *
      finePairPacketObservable a b M q C c G Φ (ζ, h)) =
      (∫ᵛ e, G ζ e.1 e.2 ∂<•finePairDensitySignedRule a b M) * responseMatrixAction q C (A ζ) c Φ := by
  rw [Fintype.sum_prod_type, finePairDensitySignedRule, atomicSignedRule_integral]
  simp only [finePairPacketWeight, finePairPacketObservable]
  have he (h : FinePairDensityIndex M) (v : HighResponseMarkIndex ι q) :
      finePairDensityWeight a b M h * highResponseMarkWeight C q (A ζ) v *
      (G ζ (finePairDensityAtom a b M h).1 (finePairDensityAtom a b M h).2 *
        Φ (coefficientReset c (highResponseMarkAtom C q v).2 (highResponseMarkAtom C q v).1)) =
      finePairDensityWeight a b M h * G ζ (finePairDensityAtom a b M h).1 (finePairDensityAtom a b M h).2 *
        (highResponseMarkWeight C q (A ζ) v *
          Φ (coefficientReset c (highResponseMarkAtom C q v).2 (highResponseMarkAtom C q v).1)) := by ring
  simp_rw [he, ← Finset.mul_sum, highResponseMark_action]
  rw [← Finset.sum_mul]
theorem finePairPacketSignedMeasure_factor_integral (σ ) [IsFiniteMeasure σ]
    (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (c : ι → ℝ) (G : Z → ℝ → ℝ → ℝ) (hG : ∀ z eps, Measurable (fun ζ => G ζ z eps))
    (L ) (hL : 0 ≤ L) (hGbound : ∀ ζ h,
      |G ζ (finePairDensityAtom a b M h).1 (finePairDensityAtom a b M h).2| ≤ L)
    (Φ R) (hΦ : ∀ h : HighResponseMarkIndex ι q,
      |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)| ≤ R) :
    (∫ᵛ e, finePairPacketObservable a b M q C c G Φ e ∂<•finePairPacketSignedMeasure σ a b M q C A) =
      ∫ ζ, (∫ᵛ e, G ζ e.1 e.2 ∂<•finePairDensitySignedRule a b M) * responseMatrixAction q C (A ζ) c Φ ∂σ := by
  have h_finePairPacketSignedMeasure_integral (f : Z × FinePairPacketIndex ι M q → ℝ) (hf : ∀ h, Measurable (fun ζ => f (ζ, h))) L (hb : ∀ ζ h, ‖f (ζ, h)‖ ≤ L) : (∫ᵛ e, f e ∂<•finePairPacketSignedMeasure σ a b M q C A) =
      ∫ ζ, ∑ h : FinePairPacketIndex ι M q, finePairPacketWeight a b M q C A (ζ, h) * f (ζ, h) ∂σ := by
    have hm := measurable_from_prod_countable_left hf
    have hw := finePairPacketWeight_integrable σ a b M q C A hA hcost
    rw [finePairPacketSignedMeasure, signedDensity_integral _ _ hw
      (finePairPacketWeight_measurable a b M q C A hA) f hm L (fun e => hb e.1 e.2),
      integral_prod _ (hw.mul_bdd hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun e => hb e.1 e.2)))]
    simp only [integral_count]
  rw [(h_finePairPacketSignedMeasure_integral _ (fun h => by
      change Measurable (fun ζ => G ζ (finePairDensityAtom a b M h.1).1
        (finePairDensityAtom a b M h.1).2 *
        Φ (coefficientReset c (highResponseMarkAtom C q h.2).2 (highResponseMarkAtom C q h.2).1))
      exact (hG _ _).mul_const _) (L * R) (fun ζ h => by
      rw [finePairPacketObservable, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hGbound ζ h.1) (hΦ h.2) (abs_nonneg _) hL))]
  simp_rw [finePairPacketObservable_finite_action]
theorem finePairPacketSignedMeasure_pair_action  (σ ) [IsFiniteMeasure σ]
    (a b ) (ha : 0 < a) (hab : a < b) (M q ) (hM : 2 ≤ M) (C A) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (c )
    (p : U → ℝ) (hp : ∀ u, p u ∈ Icc a b) (ψ : Z → U → ℝ)
    (hmψ : ∀ u, Measurable (fun ζ => ψ ζ u)) (hψ : ∀ ζ u, |ψ ζ u| ≤ 1)
    (u v : U) (Φ : (ι → ℝ) → ℝ) (R : ℝ) (hΦ : ∀ h : HighResponseMarkIndex ι q,
      |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)| ≤ R) :
    (∫ᵛ e, finePairPacketObservable a b M q C c
      (fun ζ z eps => finePairDensityReset a b z eps p (ψ ζ) u *
        finePairDensityReset a b z eps p (ψ ζ) v) Φ e
      ∂<•finePairPacketSignedMeasure σ a b M q C A) =
      p u * p v * (∫ ζ, ψ ζ u * ψ ζ v * responseMatrixAction q C (A ζ) c Φ ∂σ) := by
  have hm (z eps : ℝ) (u : U) :
      Measurable (fun ζ => finePairDensityReset a b z eps p (ψ ζ) u) := by
    exact measurable_const.add ((hmψ u).const_mul _)
  have h_finePairDensitySignedRule_pair_exact (ψ : U → ℝ) (u : U) (v : U) : (∫ᵛ e, finePairDensityReset a b e.1 e.2 p ψ u * finePairDensityReset a b e.1 e.2 p ψ v
      ∂<•finePairDensitySignedRule a b M) = p u * p v * ψ u * ψ v := by
    rw [finePairDensitySignedRule_integral a b M
      (fun z eps => finePairDensityReset a b z eps p ψ u * finePairDensityReset a b z eps p ψ v)]
    have he (z eps : ℝ) (u : U) : finePairDensityReset a b z eps p ψ u =
        z + (densityMargin a b z / b * p u * ψ u) * eps := by
      unfold finePairDensityReset
      ring
    simp_rw [he, fineModulation_quadratic]
    have hc := densityCountCoefficient_exact a b ha hab M 2 2 (by omega) (by omega) hM
    simp only [densityCountCoefficient, Nat.sub_self, pow_zero, one_mul, ite_true] at hc
    have hθ : densityMargin a b 0 ^ 2 ≠ 0 := pow_ne_zero _ (densityMargin_zero_ne a b ha hab)
    have hs := (div_eq_iff hθ).mp hc |>.trans (one_mul _)
    have hterm (j : Fin (M + 3)) : exteriorWeight a b (M + 2) j *
        ((densityMargin a b (exteriorNode a b (M + 2) j) / b * p u * ψ u) *
         (densityMargin a b (exteriorNode a b (M + 2) j) / b * p v * ψ v)) =
        exteriorWeight a b (M + 2) j * densityMargin a b (exteriorNode a b (M + 2) j) ^ 2 *
        ((p u * p v * ψ u * ψ v) / b ^ 2) := by ring
    simp_rw [hterm]
    rw [← Finset.sum_mul, hs]
    unfold finePairDensityPrefactor
    field_simp [hθ, densityMargin_zero_ne a b ha hab, (ha.trans hab).ne']
  rw [finePairPacketSignedMeasure_factor_integral σ a b M q C A hA hcost c
    (fun ζ z eps => finePairDensityReset a b z eps p (ψ ζ) u * finePairDensityReset a b z eps p (ψ ζ) v)
    (fun z eps => (hm z eps u).mul (hm z eps v)) (b ^ 2) (by positivity) (fun ζ h => by
      rw [abs_mul, pow_two]
      exact mul_le_mul (finePairFieldReset_abs_le a b ha hab M p hp ψ hψ (ζ, h) u)
        (finePairFieldReset_abs_le a b ha hab M p hp ψ hψ (ζ, h) v) (abs_nonneg _) (ha.trans hab).le) Φ R hΦ]
  simp_rw [h_finePairDensitySignedRule_pair_exact]
  have he (ζ : Z) : p u * p v * ψ ζ u * ψ ζ v * responseMatrixAction q C (A ζ) c Φ =
      (p u * p v) * (ψ ζ u * ψ ζ v * responseMatrixAction q C (A ζ) c Φ) := by ring
  simp_rw [he]
  exact integral_const_mul _ _
end Packet
theorem fineModulationNode_reflection (i : Fin 3) : fineModulationNode i.rev = -fineModulationNode i := by
  fin_cases i <;> norm_num [fineModulationNode, Fin.rev]
theorem fineModulationWeight_abs_reflection (i : Fin 3) :
    |fineModulationWeight i.rev| = |fineModulationWeight i| := by
  fin_cases i <;> norm_num [fineModulationWeight, Fin.rev]
def finePairPacketReflection (ι M q) : Equiv.Perm (FinePairPacketIndex ι M q) :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.refl _) Fin.revPerm) (Equiv.refl _)
section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
def finePairPacketMarkMass (σ : Measure Z) (a b : ℝ) (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ) : ℝ :=
  signedMarkMass (σ.prod Measure.count) (finePairPacketWeight a b M q C A)
def finePairPacketAbsoluteLaw (σ : Measure Z) (a b : ℝ) (M q ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : Measure (Z × FinePairPacketIndex ι M q) :=
  absoluteMarkLaw (σ.prod Measure.count) (finePairPacketWeight a b M q C A)
def finePairPacketActivation (σ : Measure Z) (a b : ℝ) (M q ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : Z × FinePairPacketIndex ι M q → ℝ :=
  absoluteActivation (σ.prod Measure.count) (finePairPacketWeight a b M q C A)
def finePairPacketIntercept (a b : ℝ) (M q ) (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  (finePairDensityAtom a b M e.2.1).1
def finePairPacketSlope (a b : ℝ) (M q ) (ψ : Z → ℝ) (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  densityMargin a b (finePairPacketIntercept a b M q e) / b *
    (finePairDensityAtom a b M e.2.1).2 * ψ e.1
def finePairPacketResponseVector (M q ) (C : ℝ) (e : Z × FinePairPacketIndex ι M q) : ι → ℝ :=
  (highResponseMarkAtom C q e.2.2).2
def finePairPacketResponseTime (M q ) (e : Z × FinePairPacketIndex ι M q) : ℝ :=
  (highResponseMarkAtom 0 q e.2.2).1
theorem finePairPacketSlope_joint_measurable {U : Type*} [MeasurableSpace U]
    (a b : ℝ) (M q : ℕ) (ψ : Z → U → ℝ)
    (hψ : Measurable (fun zu : Z × U => ψ zu.1 zu.2)) :
    Measurable (fun eu : (Z × FinePairPacketIndex ι M q) × U =>
      finePairPacketSlope a b M q (fun ζ => ψ ζ eu.2) eu.1) := by
  have hc : Measurable (fun eu : (Z × FinePairPacketIndex ι M q) × U =>
      densityMargin a b (finePairDensityAtom a b M eu.1.2.1).1 / b *
        (finePairDensityAtom a b M eu.1.2.1).2) :=
    (measurable_of_countable (fun h : FinePairPacketIndex ι M q =>
      densityMargin a b (finePairDensityAtom a b M h.1).1 / b *
        (finePairDensityAtom a b M h.1).2)).comp (measurable_snd.comp measurable_fst)
  exact hc.mul (hψ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
theorem finePairPacketIntercept_mem (a b ) (hab : a ≤ b) (M q )
    (e : Z × FinePairPacketIndex ι M q) : finePairPacketIntercept a b M q e ∈ Icc a b :=
  exteriorNode_mem a b hab (M + 2) e.2.1.1
theorem finePairPacketSlope_bound (a b : ℝ) (ha : 0 < a) (hab : a < b) (M q : ℕ)
    (ψ : Z → ℝ) (hψ : ∀ ζ, |ψ ζ| ≤ 1) (e : Z × FinePairPacketIndex ι M q) :
    |finePairPacketSlope a b M q ψ e| ≤ (b - a) / (4 * b) :=
  have h_finePairDensityReset_slope_bound {U} (z) (eps) (hz : z ∈ Icc a b) (heps : |eps| ≤ 1) (ψ : U → ℝ) (u : U) (hψ : |ψ u| ≤ 1) : |densityMargin a b z / b * eps * ψ u| ≤ (b - a) / (4 * b) := by
    have hh := localDensityReset_slope_bound a b ha hab 1 (by omega) z hz (fun _ => eps)
      (fun _ => heps) (fun u _ => ψ u) u (fun _ => hψ)
    simpa [mul_assoc] using hh
  (h_finePairDensityReset_slope_bound _ _ (exteriorNode_mem a b hab.le (M + 2) e.2.1.1) (fineModulationNode_bound e.2.1.2) (fun _ => ψ e.1) () (hψ e.1))
theorem finePairPacketSlope_absolute_sum_zero (a b M q C)
    (A : Z → ι → ι → ℝ) (ψ : Z → ℝ) (ζ : Z) :
    (∑ h : FinePairPacketIndex ι M q, |finePairPacketWeight a b M q C A (ζ, h)| *
      finePairPacketSlope a b M q ψ (ζ, h)) = 0 :=
  have h_finePairPacketWeight_abs_reflection {Z} {ι} (A : Z → ι → ι → ℝ) (ζ : Z) (h : FinePairPacketIndex ι M q) : |finePairPacketWeight a b M q C A (ζ, finePairPacketReflection ι M q h)| =
      |finePairPacketWeight a b M q C A (ζ, h)| := by
    simp only [finePairPacketWeight, finePairDensityWeight, finePairPacketReflection, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply, Fin.revPerm_apply, abs_mul, fineModulationWeight_abs_reflection]
  have h_finePairPacketSlope_reflection {Z} {ι} (ψ : Z → ℝ) (ζ : Z) (h : FinePairPacketIndex ι M q) : finePairPacketSlope a b M q ψ (ζ, finePairPacketReflection ι M q h) =
      -finePairPacketSlope a b M q ψ (ζ, h) := by
    simp only [finePairPacketSlope, finePairPacketIntercept, finePairDensityAtom, finePairPacketReflection, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply, Fin.revPerm_apply, fineModulationNode_reflection]
    ring
  finite_even_odd_sum_zero (finePairPacketReflection ι M q) _ _
    (h_finePairPacketWeight_abs_reflection A ζ)
    (h_finePairPacketSlope_reflection ψ ζ)
variable (σ : Measure Z) [IsFiniteMeasure σ] (a b : ℝ) (M q : ℕ) (C : ℝ)
  (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
  (hcost : Integrable (separatedMatrixCost A) σ)
  (hpos : 0 < finePairPacketMarkMass σ a b M q C A)
include hA hcost hpos
theorem finePairPacketAbsoluteLaw_probability :
    IsProbabilityMeasure (finePairPacketAbsoluteLaw σ a b M q C A) :=
  absoluteMarkLaw_probability _ _ (finePairPacketWeight_integrable σ a b M q C A hA hcost) hpos
theorem finePairPacketActivation_centered :
    (∫ e, finePairPacketActivation σ a b M q C A e ∂finePairPacketAbsoluteLaw σ a b M q C A) = 0 := by
  apply absoluteActivation_centered _ _ (finePairPacketWeight_measurable a b M q C A hA) hpos
  rw [integral_prod _ (finePairPacketWeight_integrable σ a b M q C A hA hcost)]
  simp only [integral_count]
  have hz (ζ : Z) : (∑ h : FinePairPacketIndex ι M q, finePairPacketWeight a b M q C A (ζ, h)) = 0 := by
    have hh := finePairPacketObservable_finite_action a b M q C A (fun _ => 0)
      (fun _ _ _ => 1) (fun _ => 1) ζ
    simpa only [finePairPacketObservable, mul_one, responseMatrixAction_zero_mass, mul_zero] using hh
  simp only [hz, integral_zero]
theorem finePairPacketAbsoluteLaw_slope_integral_zero (ha : 0 < a) (hab : a < b)
    (ψ ) (hmψ : Measurable ψ) (hψ : ∀ ζ, |ψ ζ| ≤ 1) :
    (∫ e, finePairPacketSlope a b M q ψ e ∂finePairPacketAbsoluteLaw σ a b M q C A) = 0 := by
  have h_finePairPacketSlope_measurable : Measurable (finePairPacketSlope (ι := ι) a b M q ψ) := by
    apply measurable_from_prod_countable_left
    intro h
    unfold finePairPacketSlope finePairPacketIntercept
    dsimp only
    exact hmψ.const_mul _
  have hi := (finePairPacketWeight_integrable σ a b M q C A hA hcost).abs.mul_bdd
    h_finePairPacketSlope_measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => by
      simpa only [Real.norm_eq_abs] using finePairPacketSlope_bound a b ha hab M q ψ hψ e))
  rw [finePairPacketAbsoluteLaw, absoluteMarkLaw_integral _ _
    (finePairPacketWeight_measurable a b M q C A hA) hpos, integral_prod _ hi]
  simp only [integral_count, finePairPacketSlope_absolute_sum_zero, integral_zero, zero_div]
end Packet
abbrev FinePairFieldMark (d : ℕ) := partitionFieldMark (Covariate d × ℝ)
theorem boundedHyperplaneFieldValue_section_measurable (d : ℕ) (u : Covariate d) :
    Measurable (fun z : FinePairFieldMark d => boundedHyperplaneFieldValue z u) :=
  (boundedHyperplaneFieldValue_measurable d).comp (measurable_id.prodMk measurable_const)
def finePairFieldKernel (d ) : Kernel ℝ (FinePairFieldMark d) where
  toFun := boundedHyperplaneFieldLaw d
  measurable' := boundedHyperplaneFieldLaw_measurable d
instance finePairFieldKernel_markov (d : ℕ) [NeZero d] : IsMarkovKernel (finePairFieldKernel d) :=
  ⟨fun T => boundedHyperplaneFieldLaw_probability d T⟩
def finePairTimeFieldMeasure (d ) (lo hi : ℝ) : Measure (ℝ × FinePairFieldMark d) :=
  (volume.restrict (Icc lo hi)).compProd (finePairFieldKernel d)
instance finePairTimeFieldMeasure_finite (d : ℕ) [NeZero d] (lo hi : ℝ) :
    IsFiniteMeasure (finePairTimeFieldMeasure d lo hi) := by
  unfold finePairTimeFieldMeasure
  infer_instance
theorem finePairTimeFieldMeasure_integral (d ) [NeZero d] (lo hi )
    (f : ℝ × FinePairFieldMark d → ℝ) (hf : Integrable f (finePairTimeFieldMeasure d lo hi)) :
    (∫ e, f e ∂finePairTimeFieldMeasure d lo hi) =
      ∫ T in Icc lo hi, ∫ z, f (T,z) ∂boundedHyperplaneFieldLaw d T :=
  Measure.integral_compProd hf
def finePairTimeFieldValue  (e : ℝ × FinePairFieldMark d) (u : Covariate d) : ℝ :=
  boundedHyperplaneFieldValue e.2 u
theorem finePairTimeFieldValue_abs {d : ℕ} (e : ℝ × FinePairFieldMark d) (u : Covariate d) :
    |finePairTimeFieldValue e u| = 1 := boundedHyperplaneFieldValue_abs _ _
theorem finePairTimeFieldMeasure_ae_time (d ) [NeZero d] (lo hi ) :
    ∀ᵐ e ∂finePairTimeFieldMeasure d lo hi, e.1 ∈ Icc lo hi :=
  Measure.ae_compProd_of_ae_fst (finePairFieldKernel d) measurableSet_Icc
    (ae_restrict_mem measurableSet_Icc)
theorem finePairTimeFieldMeasure_fst_integrable (d ) [NeZero d] (lo hi ) :
    Integrable (fun e => e.1) (finePairTimeFieldMeasure d lo hi) := by
  apply (integrable_const (max |lo| |hi|)).mono' measurable_fst.aestronglyMeasurable
  filter_upwards [finePairTimeFieldMeasure_ae_time d lo hi] with e he
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [neg_abs_le lo, le_max_left |lo| |hi|, he.1],
    by linarith [le_abs_self hi, le_max_right |lo| |hi|, he.2]⟩
section Matrix
variable {ι : Type*} [Fintype ι]
def finePairTimeMatrix (d ) (A : ι → ι → ℝ) (e : ℝ × FinePairFieldMark d) : ι → ι → ℝ :=
  fun i j => e.1 * A i j
theorem finePairTimeMatrix_measurable (d : ℕ) (A : ι → ι → ℝ) (i j : ι) :
    Measurable (fun e => finePairTimeMatrix d A e i j) := measurable_fst.mul_const _
theorem finePairTimeMatrix_cost (d ) (A : ι → ι → ℝ) (e : ℝ × FinePairFieldMark d) :
    separatedMatrixCost (finePairTimeMatrix d A) e =
      |e.1| * (∑ i, ∑ j, |A i j|) := by
  simp only [separatedMatrixCost, finePairTimeMatrix, abs_mul, Finset.mul_sum]
theorem finePairTimeMatrix_cost_integrable (d : ℕ) [NeZero d] (lo hi : ℝ) (A : ι → ι → ℝ) :
    Integrable (separatedMatrixCost (finePairTimeMatrix d A)) (finePairTimeFieldMeasure d lo hi) := by
  change Integrable (fun e => separatedMatrixCost (finePairTimeMatrix d A) e) _
  simp only [finePairTimeMatrix_cost]
  exact (finePairTimeFieldMeasure_fst_integrable d lo hi).abs.mul_const _
end Matrix
theorem finePairTimeFieldValue_weighted_covariance (d ) [NeZero d] (lo hi )
    (hlo : 0 ≤ lo) (u v : Covariate d) (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d) :
    (∫ e, e.1 * (finePairTimeFieldValue e u * finePairTimeFieldValue e v)
      ∂finePairTimeFieldMeasure d lo hi) =
      ∫ T in Icc lo hi, T * Real.exp (-T * euclideanNorm (fun r => u r - v r)) := by
  have h_finePairTimeFieldValue_weighted_pair_integrable : Integrable (fun e => e.1 * (finePairTimeFieldValue e u * finePairTimeFieldValue e v))
      (finePairTimeFieldMeasure d lo hi) := by
    have hm (u : Covariate d) : Measurable (fun e : ℝ × FinePairFieldMark d =>
        finePairTimeFieldValue e u) :=
      (boundedHyperplaneFieldValue_section_measurable d u).comp measurable_snd
    exact (finePairTimeFieldMeasure_fst_integrable d lo hi).mul_bdd (c := 1)
      ((hm u).mul (hm v)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun e => by
        simp only [Real.norm_eq_abs, abs_mul, finePairTimeFieldValue_abs, one_mul, le_refl]))
  rw [finePairTimeFieldMeasure_integral d lo hi _
    h_finePairTimeFieldValue_weighted_pair_integrable]
  simp only [finePairTimeFieldValue, integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
  have h_boundedHyperplaneField_covariance : (∫ z, boundedHyperplaneFieldValue z u * boundedHyperplaneFieldValue z v
      ∂boundedHyperplaneFieldLaw d T) =
      Real.exp (-T * euclideanNorm (fun r => u r - v r)) := by
    have hT  := hlo.trans hT.1
    simp only [boundedHyperplaneFieldLaw, boundedHyperplaneFieldValue]
    rw [poissonCellField_covariance _ _ _ hyperplaneHalfspace_measurable,
      gaussianHyperplaneLaw_same_complement, gaussianHyperplaneLaw_separation_real d u v hu hv, Real.coe_toNNReal (2 * ↑d * T) (by positivity)]
    congr 1
    have : ↑d ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    field_simp
  rw [h_boundedHyperplaneField_covariance]
end
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
  | .unit => highPacketAbsoluteLaw (Measure.dirac ()) a b D 2 D q C
      (fun _ => finePairUnitMatrix d D)
  | .coarse => highPacketAbsoluteLaw (finePairTimeFieldMeasure d 0 T₀) a b D 2 D q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))
  | .fine => finePairPacketAbsoluteLaw (finePairTimeFieldMeasure d T₀ N) a b M q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))
def finePairRowMass (d D M q : ℕ) (a b C T₀ N : ℝ) : FinePairRowTag → ℝ
  | .unit => highPacketMarkMass (Measure.dirac ()) a b D 2 D q C
      (fun _ => finePairUnitMatrix d D)
  | .coarse => highPacketMarkMass (finePairTimeFieldMeasure d 0 T₀) a b D 2 D q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))
  | .fine => finePairPacketMarkMass (finePairTimeFieldMeasure d T₀ N) a b M q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))
def finePairRowActivation (d D M q : ℕ) (a b C T₀ N : ℝ) :
    (i : FinePairRowTag) → FinePairRowMark d D M q i → ℝ
  | .unit => highPacketActivation (Measure.dirac ()) a b D 2 D q C
      (fun _ => finePairUnitMatrix d D)
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
def finePairRowData (d k D M q ) (a b C T₀ N : ℝ) :
    HighUnionRowData d k D FinePairRowTag (FinePairRowMark d D M q) where
  rowLaw := finePairRowLaw d D M q a b C T₀ N
  rowMass := finePairRowMass d D M q a b C T₀ N
  rowActivation := finePairRowActivation d D M q a b C T₀ N
  rowIntercept := finePairRowIntercept d D M q a b
  rowSlope := finePairRowSlope d k D M q a b
  rowVector := finePairRowVector d D M q C
  rowTime := finePairRowTime d D M q
theorem finePairRowMass_nonneg (d D M q a b C T₀ N i) :
    0 ≤ finePairRowMass d D M q a b C T₀ N i := by
  cases i <;> exact signedMarkMass_nonneg _ _
end NearlyMinimax
