module
public import Mathlib
public import NearlyMinimax.Model
@[expose] public section
noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

variable {ι Ω : Type*} {d : ℕ}
def projectionEnergy  [Fintype ι] (x : ι → ℝ) : ℝ := x ⬝ᵥ x
def projectionQuadratic  [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x)
def projectionEstimator  [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  projectionQuadratic A x / A.trace
theorem projectionEnergy_nonneg  [Fintype ι] (x : ι → ℝ) :
    0 ≤ projectionEnergy x := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
theorem projection_quadratic_eq_energy  [Fintype ι]
    (A : Matrix ι ι ℝ) (hsym : Aᵀ = A) (hidem : A * A = A) (f : ι → ℝ) :
    projectionQuadratic A f = projectionEnergy (A *ᵥ f) := by
  unfold projectionQuadratic projectionEnergy
  symm
  rw [dotProduct_mulVec, ← mulVec_transpose, hsym, mulVec_mulVec, hidem, dotProduct_comm]
theorem projection_energy_le  [Fintype ι]
    (A : Matrix ι ι ℝ) (hsym : Aᵀ = A) (hidem : A * A = A) (f : ι → ℝ) :
    projectionEnergy (A *ᵥ f) ≤ projectionEnergy f := by
  have h_projection_orthogonal : (A *ᵥ f) ⬝ᵥ (f - A *ᵥ f) = 0 := by
    rw [dotProduct_sub]
    have h := projection_quadratic_eq_energy A hsym hidem f
    unfold projectionQuadratic projectionEnergy at h
    rw [dotProduct_comm (A *ᵥ f) f, h, sub_self]
  have horth := h_projection_orthogonal
  have := projectionEnergy_nonneg (f - A *ᵥ f)
  have : projectionEnergy f = projectionEnergy (A *ᵥ f) +
      projectionEnergy (f - A *ᵥ f) := by
    have hid : f = A *ᵥ f + (f - A *ᵥ f) := by abel
    conv_lhs => rw [hid]
    unfold projectionEnergy
    rw [dotProduct_add, add_dotProduct, add_dotProduct, horth,
      dotProduct_comm (f - A *ᵥ f) (A *ᵥ f), horth]
    ring
  linarith
theorem projection_approximation_bound  [Fintype ι]
    (A : Matrix ι ι ℝ) (hsym : Aᵀ = A) (hidem : A * A = A)
    (f q ) (hq : A *ᵥ q = 0) (b ) (hb : 0 ≤ b)
    (happrox : ∀ i, |f i - q i| ≤ b) :
    projectionEnergy (A *ᵥ f) ≤ Fintype.card ι * b ^ 2 := by
  have h_projection_residual_minimality : projectionEnergy (A *ᵥ f) ≤ projectionEnergy (f - q) := by
    have hAq : A *ᵥ (f - q) = A *ᵥ f := by rw [mulVec_sub, hq, sub_zero]
    rw [← hAq]
    exact projection_energy_le A hsym hidem (f - q)
  apply h_projection_residual_minimality.trans
  calc
    (∑ i, (f - q) i * (f - q) i) ≤ ∑ _i : ι, b ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hs := (sq_le_sq₀ (abs_nonneg _) hb).mpr (happrox i)
      rw [sq_abs] at hs
      simpa only [Pi.sub_apply, pow_two] using hs
    _ = _ := by simp
theorem projection_quadratic_add  [Fintype ι]
    (A ) (hsym : Aᵀ = A) (f ε : ι → ℝ) :
    projectionQuadratic A (f + ε) = projectionQuadratic A f +
      2 * (A *ᵥ f) ⬝ᵥ ε + projectionQuadratic A ε := by
  unfold projectionQuadratic
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct]
  have hcross : f ⬝ᵥ (A *ᵥ ε) = (A *ᵥ f) ⬝ᵥ ε := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym]
  rw [hcross, dotProduct_comm ε (A *ᵥ f)]
  ring
theorem projection_quadratic_sum  [Fintype ι]
    (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    projectionQuadratic A x = ∑ i, ∑ j, A i j * x i * x j := by
  unfold projectionQuadratic mulVec dotProduct
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring
theorem projection_coordinate_covariance  [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ε : Ω → ι → ℝ) (V : ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hind : iIndepFun (fun i ω => ε ω i) μ)
    (hmean : ∀ i, (∫ ω, ε ω i ∂μ) = 0)
    (hsecond : ∀ i, (∫ ω, (ε ω i) ^ 2 ∂μ) = V) :
    ∀ i j, (∫ ω, ε ω i * ε ω j ∂μ) = if i = j then V else 0 := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp only [← pow_two]
    exact hsecond i
  · simp only [if_neg hij]
    have hi := (hind.indepFun hij).integral_mul_eq_mul_integral
      (hε i).aestronglyMeasurable (hε j).aestronglyMeasurable
    simpa only [Pi.mul_apply, hmean, mul_zero] using hi
theorem projection_complement  [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hsym : Pᵀ = P) (hidem : P * P = P) :
    (1 - P)ᵀ = 1 - P ∧ (1 - P) * (1 - P) = 1 - P := by
  constructor
  · rw [transpose_sub, transpose_one, hsym]
  · rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, hidem]
    abel
theorem projection_quadratic_memLp_two_of_products  [Fintype ι]
    [MeasurableSpace Ω] (μ : Measure Ω) (A : Matrix ι ι ℝ) (ε : Ω → ι → ℝ)
    (hproducts : ∀ i j, MemLp (fun ω => ε ω i * ε ω j) 2 μ) :
    MemLp (fun ω => projectionQuadratic A (ε ω)) 2 μ := by
  simp_rw [projection_quadratic_sum]
  apply memLp_finset_sum
  intro i hi
  apply memLp_finset_sum
  intro j hj
  simpa only [mul_assoc] using (hproducts i j).const_mul (A i j)
theorem projection_estimator_memLp_two  [Fintype ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix ι ι ℝ) (hsym : Aᵀ = A) (f : ι → ℝ) (ε : Ω → ι → ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hproducts : ∀ i j, MemLp (fun ω => ε ω i * ε ω j) 2 μ) :
    MemLp (fun ω => projectionEstimator A (f + ε ω)) 2 μ := by
  have hsum : MemLp (fun ω => projectionQuadratic A f +
      2 * (A *ᵥ f) ⬝ᵥ ε ω + projectionQuadratic A (ε ω)) 2 μ :=
    ((memLp_const (projectionQuadratic A f)).add ((memLp_finset_sum Finset.univ (fun i _ => (hε i).const_mul ((A *ᵥ f) i))).const_mul 2)).add (projection_quadratic_memLp_two_of_products μ A ε hproducts)
  simpa only [projectionEstimator, projection_quadratic_add A hsym f,
    div_eq_mul_inv, mul_comm] using hsum.const_mul A.trace⁻¹
theorem projection_estimator_mse_bound
     [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Matrix ι ι ℝ)
    (hsym : Aᵀ = A) (hidem : A * A = A) (hd : 0 < A.trace)
    (f : ι → ℝ) (ε : Ω → ι → ℝ) (V C : ℝ) (c : ι → ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hmean : ∀ i, (∫ ω, ε ω i ∂μ) = 0)
    (hsecond : ∀ i j, (∫ ω, ε ω i * ε ω j ∂μ) = if i = j then V else 0)
    (hproducts : ∀ i j, MemLp (fun ω => ε ω i * ε ω j) 2 μ)
    (hcov : ∀ i j k l,
      covariance (fun ω => ε ω i * ε ω j) (fun ω => ε ω k * ε ω l) μ =
        (if i = k ∧ j = l then (if i = j then c i else V ^ 2) else 0) +
        (if i = l ∧ j = k ∧ i ≠ j then V ^ 2 else 0))
    (hc : ∀ i, c i ≤ C) (hV : 2 * V ^ 2 ≤ C) :
    (∫ ω, (projectionEstimator A (f + ε ω) - V) ^ 2 ∂μ) ≤
      (2 * C * A.trace + 8 * V * projectionEnergy (A *ᵥ f)) / A.trace ^ 2 +
        (projectionEnergy (A *ᵥ f) / A.trace) ^ 2 := by
  have h_projection_noise_expectation (A : Matrix ι ι ℝ) (ε : Ω → ι → ℝ) (V : ℝ) (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ) (hcov : ∀ i j, (∫ ω, ε ω i * ε ω j ∂μ) = if i = j then V else 0) : (∫ ω, projectionQuadratic A (ε ω) ∂μ) = V * A.trace := by
    have hij (i j : ι) : Integrable (fun ω => A i j * ε ω i * ε ω j) μ := by
      convert ((hε i).integrable_mul (hε j)).const_mul (A i j) using 1
      funext ω
      simp [mul_assoc]
    simp_rw [projection_quadratic_sum]
    rw [integral_finset_sum Finset.univ (fun i _ => integrable_finset_sum _ (fun j _ => hij i j))]
    simp_rw [integral_finset_sum Finset.univ (fun j _ => hij _ j), mul_assoc,
      integral_const_mul, hcov, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    unfold trace diag
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have h_projection_linear_noise_expectation (x : ι → ℝ) (ε : Ω → ι → ℝ) (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ) (hmean : ∀ i, (∫ ω, ε ω i ∂μ) = 0) : (∫ ω, x ⬝ᵥ ε ω ∂μ) = 0 := by
    unfold dotProduct
    rw [integral_finset_sum Finset.univ (fun i _ =>
      ((hε i).integrable (by norm_num)).const_mul (x i))]
    simp_rw [integral_const_mul, hmean, mul_zero]
    simp
  have h_projection_estimator_expectation : (∫ ω, projectionEstimator A (f + ε ω) ∂μ) =
      V + projectionEnergy (A *ᵥ f) / A.trace := by
    have hlin : Integrable (fun ω => (A *ᵥ f) ⬝ᵥ ε ω) μ := by
      apply integrable_finset_sum
      intro i hi
      exact ((hε i).integrable (by norm_num)).const_mul ((A *ᵥ f) i)
    have h_projection_quadratic_integrable : Integrable (fun ω => projectionQuadratic A (ε ω)) μ := by
      simp_rw [projection_quadratic_sum]
      apply integrable_finset_sum
      intro i hi
      apply integrable_finset_sum
      intro j hj
      convert ((hε i).integrable_mul (hε j)).const_mul (A i j) using 1
      funext ω
      simp [mul_assoc]
    have hquad := h_projection_quadratic_integrable
    have hsum : Integrable (fun ω => projectionQuadratic A f + 2 * (A *ᵥ f) ⬝ᵥ ε ω) μ :=
      (integrable_const (projectionQuadratic A f)).add (hlin.const_mul 2)
    simp_rw [projectionEstimator, projection_quadratic_add A hsym f]
    rw [integral_div, integral_add hsum hquad,
      integral_add (integrable_const (projectionQuadratic A f)) (hlin.const_mul 2), integral_const,
      probReal_univ, one_smul, integral_const_mul,
      h_projection_linear_noise_expectation (A *ᵥ f) ε hε hmean,
      mul_zero, add_zero, h_projection_noise_expectation A ε V hε hsecond,
      projection_quadratic_eq_energy A hsym hidem f]
    field_simp
    ring
  have h_projection_mse_decomposition (X : Ω → ℝ) (hX : MemLp X 2 μ) : (∫ ω, (X ω - V) ^ 2 ∂μ) = variance X μ + ((∫ ω, X ω ∂μ) - V) ^ 2 := by
    have hvar := variance_eq_sub (hX.sub (memLp_const V))
    change variance (fun ω => X ω - V) μ =
      (∫ ω, (X ω - V) ^ 2 ∂μ) - (∫ ω, X ω - V ∂μ) ^ 2 at hvar
    have hmean : (∫ ω, X ω - V ∂μ) = (∫ ω, X ω ∂μ) - V := by
      rw [integral_sub (hX.integrable (by norm_num)) (integrable_const V)]
      simp
    rw [variance_sub_const hX.aestronglyMeasurable V, hmean] at hvar
    linarith
  rw [h_projection_mse_decomposition _ (projection_estimator_memLp_two μ A hsym f ε hε hproducts),
    h_projection_estimator_expectation,
    add_sub_cancel_left]
  have h_projection_estimator_variance_bound : variance (fun ω => projectionEstimator A (f + ε ω)) μ ≤
      (2 * C * A.trace + 8 * V * projectionEnergy (A *ᵥ f)) / A.trace ^ 2 := by
    have hlin : MemLp (fun ω => (A *ᵥ f) ⬝ᵥ ε ω) 2 μ := by
      exact memLp_finset_sum Finset.univ (fun i _ => (hε i).const_mul ((A *ᵥ f) i))
    have hquad := projection_quadratic_memLp_two_of_products μ A ε hproducts
    have hlinvar : variance (fun ω => (A *ᵥ f) ⬝ᵥ ε ω) μ =
        V * projectionEnergy (A *ᵥ f) := by
      rw [variance_of_integral_eq_zero hlin.aemeasurable
        (h_projection_linear_noise_expectation (A *ᵥ f) ε hε hmean)]
      have hid (v : ι → ℝ) : projectionQuadratic (vecMulVec (A *ᵥ f) (A *ᵥ f)) v = ((A *ᵥ f) ⬝ᵥ v) ^ 2 := by
        unfold projectionQuadratic
        rw [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, dotProduct_comm v (A *ᵥ f)]
        simp only [smul_eq_mul, pow_two]
      have he := h_projection_noise_expectation (vecMulVec (A *ᵥ f) (A *ᵥ f)) ε V hε hsecond
      simp_rw [hid] at he
      simpa only [trace_vecMulVec, projectionEnergy] using he
    have h_projection_variance_add_le (X : Ω → ℝ) (Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) : variance (fun ω => X ω + Y ω) μ ≤ 2 * variance X μ + 2 * variance Y μ := by
      have hn := variance_nonneg (fun ω => X ω - Y ω) μ
      rw [variance_fun_sub hX hY] at hn
      rw [variance_fun_add hX hY]
      linarith
    have hnum := h_projection_variance_add_le (fun ω => 2 * (A *ᵥ f) ⬝ᵥ ε ω) (fun ω => projectionQuadratic A (ε ω)) (hlin.const_mul 2) hquad
    rw [variance_const_mul, hlinvar] at hnum
    have h_projection_quadratic_variance_bound : variance (fun ω => projectionQuadratic A (ε ω)) μ ≤ C * A.trace := by
      have h_projection_sum_squares_eq_trace : (∑ i, ∑ j, A i j ^ 2) = A.trace := by
        calc
          (∑ i, ∑ j, A i j ^ 2) = (A * A).trace := by
            unfold trace diag
            apply Finset.sum_congr rfl
            intro i hi
            rw [mul_apply]
            apply Finset.sum_congr rfl
            intro j hj
            have hs : A j i = A i j := congrArg (fun M => M i j) hsym
            rw [hs, pow_two]
          _ = A.trace := by rw [hidem]
      have h_projection_quadratic_variance_from_product_covariances : variance (fun ω => projectionQuadratic A (ε ω)) μ =
          ∑ i, ∑ j, A i j ^ 2 * (if i = j then c i else 2 * V ^ 2) := by
        have hexp : (fun ω => projectionQuadratic A (ε ω)) =
            (fun ω => ∑ p : ι × ι, A p.1 p.2 * (ε ω p.1 * ε ω p.2)) := by
          funext ω
          rw [Fintype.sum_prod_type, projection_quadratic_sum]
          simp only [mul_assoc]
        rw [hexp, variance_fun_sum (fun (p : ι × ι) => (hproducts p.1 p.2).const_mul (A p.1 p.2))]
        simp_rw [covariance_const_mul_left, covariance_const_mul_right, hcov]
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [Fintype.sum_prod_type]
        have hs : A j i = A i j := congrArg (fun M => M i j) hsym
        simp only [ite_and, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [hs]
        by_cases hij : i = j
        · simp [hij, Finset.sum_ite_irrel, Finset.sum_ite_eq, pow_two]
          ring
        · simp [hij, Finset.sum_ite_irrel, Finset.sum_ite_eq, pow_two]
          ring
      rw [h_projection_quadratic_variance_from_product_covariances,
        ← h_projection_sum_squares_eq_trace, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have : (if i = j then c i else 2 * V ^ 2) ≤ C := by
        split_ifs
        · exact hc i
        · exact hV
      nlinarith [sq_nonneg (A i j)]
    have hqbound := h_projection_quadratic_variance_bound
    have hsum : MemLp (fun ω => 2 * (A *ᵥ f) ⬝ᵥ ε ω + projectionQuadratic A (ε ω)) 2 μ :=
      (hlin.const_mul 2).add hquad
    have hvar : variance (fun ω => projectionEstimator A (f + ε ω)) μ =
        A.trace⁻¹ ^ 2 * variance
          (fun ω => 2 * (A *ᵥ f) ⬝ᵥ ε ω + projectionQuadratic A (ε ω)) μ := by
      simp_rw [projectionEstimator, projection_quadratic_add A hsym f, add_assoc,
        div_eq_mul_inv, mul_comm _ A.trace⁻¹]
      rw [variance_const_mul, variance_const_add hsum.aestronglyMeasurable]
    rw [hvar]
    calc
      _ ≤ A.trace⁻¹ ^ 2 * (2 * C * A.trace + 8 * V * projectionEnergy (A *ᵥ f)) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hnum, hqbound]) (sq_pos_of_pos (inv_pos.mpr hd)).le
      _ = _ := by rw [inv_pow, div_eq_mul_inv]; ring
  exact add_le_add
    h_projection_estimator_variance_bound le_rfl
theorem euclideanNorm_pos_of_ne_zero  (x : Covariate d) (hx : x ≠ 0) :
    0 < euclideanNorm x := by
  have hne : euclideanNorm x ≠ 0 := by
    intro hz
    have h_euclideanNorm_eq_zero_iff : euclideanNorm x = 0 ↔ x = 0 := by
      have h_euclideanNorm_eq_sqrt_energy : euclideanNorm x = Real.sqrt (projectionEnergy x) := by
        simp only [euclideanNorm, projectionEnergy, dotProduct, pow_two]
      rw [h_euclideanNorm_eq_sqrt_energy, Real.sqrt_eq_zero (projectionEnergy_nonneg x)]
      exact dotProduct_self_eq_zero
    exact hx (h_euclideanNorm_eq_zero_iff.mp hz)
  exact lt_of_le_of_ne (by unfold euclideanNorm; positivity) hne.symm
theorem holderNorm_derivative_bound  (U F ℓ α H) (hH : 0 ≤ H)
    (hNorm : holderNorm U F ℓ α ≤ ENNReal.ofReal H)
    (γ : Fin d → Fin (ℓ + 1)) (hγ : (∑ i, (γ i).val) ≤ ℓ)
    (x : Covariate d) (hx : x ∈ U) :
    |multiPartial F (fun i => (γ i).val) x| ≤ H := by
  have hterm : derivativeSup U (multiPartial F (fun i => (γ i).val)) ≤
      holderNorm U F ℓ α := by
    apply le_trans _ (le_add_right le_rfl)
    have ht := Finset.single_le_sum
      (fun δ (_ : δ ∈ Finset.univ) => (bot_le : (0 : ENNReal) ≤
        if (∑ i, (δ i).val) ≤ ℓ then derivativeSup U (multiPartial F (fun i => (δ i).val)) else 0))
      (Finset.mem_univ γ)
    simpa only [if_pos hγ] using ht
  exact (ENNReal.ofReal_le_ofReal_iff hH).mp (((le_iSup (fun z : U => ENNReal.ofReal |multiPartial F (fun i => (γ i).val) z|) ⟨x, hx⟩).trans hterm).trans hNorm)
theorem admissible_regression_value_bound  (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (x ) (hx : x ∈ unitCube d) : |θ.regression x| ≤ C.holderBound := by
  rcases hθ with ⟨_, _, _, _, ⟨F, hcube, _, hNorm⟩, _, _, _⟩
  have hb := holderNorm_derivative_bound C.domain F C.order C.alpha C.holderBound
    C.holderBound_pos.le hNorm (fun _ => 0) (by simp) x (C.cube_subset hx)
  have h_multiPartial_zero_index (F : Covariate d → ℝ) : multiPartial F (fun _ => 0) = F := by
    have hflat : (List.finRange d).flatMap (fun _ => ([] : List (Fin d))) = [] :=
      List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
    simp [multiPartial, hflat]
  simpa only [Fin.val_zero, h_multiPartial_zero_index, hcube x hx] using hb
theorem euclideanNorm_le_coordinate_radius  (x : Covariate d)
    (h : ℝ) (hh : 0 ≤ h) (hx : ∀ i, |x i| ≤ h) :
    euclideanNorm x ≤ Real.sqrt ↑d * h := by
  rw [euclideanNorm, Real.sqrt_le_iff]
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) hh, ?_⟩
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  calc
    (∑ i, x i ^ 2) ≤ ∑ _i : Fin d, h ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hh).mpr (hx i)
    _ = _ := by simp
theorem holderNorm_order_zero  (U : Set (Covariate d))
    (F : Covariate d → ℝ) (α : ℝ) :
    holderNorm U F 0 α = derivativeSup U F + holderSeminorm U F α := by
  simp [holderNorm, multiPartial, List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)]
end NearlyMinimax
