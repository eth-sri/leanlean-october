module
public import NearlyMinimax.GridProjection
public import NearlyMinimax.CellPolynomialProjection
public import NearlyMinimax.HolderTaylorBridge
public import NearlyMinimax.ConditionalLaw
public import NearlyMinimax.ParametricLower
public import NearlyMinimax.PaperGoals
@[expose] public section
noncomputable section
open Matrix MeasureTheory ProbabilityTheory MvPolynomial Filter
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1000000

variable {ι Ω : Type*}
theorem independent_error_fourth_product  [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ε : ι → Ω → ℝ) (hind : iIndepFun ε μ)
    (hmeas : ∀ i, AEStronglyMeasurable (ε i) μ)
    (hmean : ∀ i, (∫ ω, ε i ω ∂μ) = 0) (V : ℝ)
    (hsecond : ∀ i, (∫ ω, ε i ω ^ 2 ∂μ) = V) (i j k l : ι) :
    (∫ ω, ε i ω * ε j ω * ε k ω * ε l ω ∂μ) =
      if i = j then
        if k = l then (if i = k then (∫ ω, ε i ω ^ 4 ∂μ) else V ^ 2) else 0
      else if i = k ∧ j = l then V ^ 2
      else if i = l ∧ j = k then V ^ 2 else 0 := by
  have h_independent_error_list_moment (l : List ι) : (∫ ω, (l.map (fun i => ε i ω)).prod ∂μ) =
      ∏ i ∈ l.toFinset, ∫ ω, ε i ω ^ l.count i ∂μ := by
    have hid (ω : Ω) : (l.map (fun i => ε i ω)).prod = ∏ i : ι, ε i ω ^ l.count i := by
      rw [Finset.prod_list_map_count]
      apply Finset.prod_subset (Finset.subset_univ l.toFinset)
      intro i hi hin
      have hn : i ∉ l := by simpa using hin
      rw [List.count_eq_zero.mpr hn, pow_zero]
    simp_rw [hid]
    have hiPow : iIndepFun (fun i ω => ε i ω ^ l.count i) μ :=
      hind.comp (fun i x => x ^ l.count i) (fun i => measurable_id.pow_const _)
    rw [hiPow.integral_fun_prod_eq_prod_integral (fun i => (hmeas i).pow _)]
    symm
    apply Finset.prod_subset (Finset.subset_univ l.toFinset)
    intro i hi hin
    simp only [List.count_eq_zero.mpr (by simpa using hin), pow_zero]
    simp
  have he := h_independent_error_list_moment [i, j, k, l]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at he
  simp_rw [← mul_assoc] at he
  rw [he]
  by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hil : i = l <;>
    by_cases hjk : j = k <;> by_cases hjl : j = l <;> by_cases hkl : k = l <;>
    subst_vars <;>
    simp_all [List.toFinset_cons, List.toFinset_nil, List.count_cons, List.count_nil,
      Finset.prod_insert, Finset.prod_singleton, pow_one, pow_two] <;>
    simp_all [eq_comm, pow_two]
  all_goals exact Or.inl (hsecond _)
theorem independent_error_product_memLp_two  [MeasurableSpace Ω]
    (μ : Measure Ω) (ε : ι → Ω → ℝ)
    (hε : ∀ i, MemLp (ε i) 4 μ) (i j : ι) :
    MemLp (fun ω => ε i ω * ε j ω) 2 μ := by
  letI : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [← two_mul, show (4 : ENNReal) = 2 * 2 by norm_num,
      ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]⟩
  convert (hε j).mul (r := 2) (hε i) using 1
  funext ω
  simp [mul_comm]
theorem independent_error_product_covariance  [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ε : ι → Ω → ℝ) (hind : iIndepFun ε μ) (hε : ∀ i, MemLp (ε i) 4 μ)
    (hmean : ∀ i, (∫ ω, ε i ω ∂μ) = 0) (V : ℝ)
    (hsecond : ∀ i, (∫ ω, ε i ω ^ 2 ∂μ) = V) (i j k l : ι) :
    covariance (fun ω => ε i ω * ε j ω) (fun ω => ε k ω * ε l ω) μ =
      (if i = k ∧ j = l then
        (if i = j then (∫ ω, ε i ω ^ 4 ∂μ) - V ^ 2 else V ^ 2) else 0) +
      (if i = l ∧ j = k ∧ i ≠ j then V ^ 2 else 0) := by
  have htwo (i : ι) : MemLp (ε i) 2 μ := (hε i).mono_exponent (by norm_num)
  have hcov := projection_coordinate_covariance μ (fun ω i => ε i ω) V htwo hind hmean hsecond
  rw [covariance_eq_sub (independent_error_product_memLp_two μ ε hε i j)
    (independent_error_product_memLp_two μ ε hε k l)]
  simp only [Pi.mul_apply]
  simp_rw [← mul_assoc]
  rw [independent_error_fourth_product μ ε hind (fun i => (hε i).aestronglyMeasurable)
    hmean V hsecond i j k l, hcov i j, hcov k l]
  clear hcov htwo hε hind hmean hsecond
  by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hil : i = l <;>
    by_cases hjk : j = k <;> by_cases hjl : j = l <;> by_cases hkl : k = l <;>
    subst_vars <;> simp_all [eq_comm, pow_two]
theorem projection_half_degrees_risk_algebra {n d e b H V C : ℝ}
    (hn : 0 < n) (hd : 0 < d) (hdegree : n / 2 ≤ d)
    (he : 0 ≤ e) (heH : e ≤ n * H ^ 2) (heb : e ≤ n * b ^ 2)
    (hV : 0 ≤ V) (hC : 0 ≤ C) :
    (2 * C * d + 8 * V * e) / d ^ 2 + (e / d) ^ 2 ≤
      (4 * C + 32 * V * H ^ 2) / n + 4 * b ^ 4 := by
  have hnsq : n ^ 2 ≤ 4 * d ^ 2 := by
    have := (sq_le_sq₀ hn.le (by positivity)).mpr (by linarith)
    nlinarith
  have : 2 * C * n * d ≤ 4 * C * d ^ 2 := by
    have := mul_nonneg (mul_nonneg hC hd.le) (by linarith : 0 ≤ 2 * d - n)
    nlinarith
  have : 8 * V * n * e ≤ 8 * V * n ^ 2 * H ^ 2 := by
    have := mul_le_mul_of_nonneg_left heH (by positivity)
    nlinarith
  have : 8 * V * n ^ 2 * H ^ 2 ≤ 32 * V * d ^ 2 * H ^ 2 := by
    have := mul_le_mul_of_nonneg_left hnsq (by positivity : 0 ≤ 8 * V * H ^ 2)
    nlinarith
  have := (sq_le_sq₀ he (mul_nonneg hn.le (sq_nonneg b))).mpr heb
  have : n * e ^ 2 ≤ n * n ^ 2 * b ^ 4 := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (by nlinarith) hn.le
  have : n * n ^ 2 * b ^ 4 ≤ 4 * n * d ^ 2 * b ^ 4 := by
    have := mul_le_mul_of_nonneg_left hnsq (by positivity)
    nlinarith
  have hlhs : (2 * C * d + 8 * V * e) / d ^ 2 + (e / d) ^ 2 =
      (2 * C * d + 8 * V * e + e ^ 2) / d ^ 2 := by
    rw [div_pow, ← add_div]
  have hrhs : (4 * C + 32 * V * H ^ 2) / n + 4 * b ^ 4 =
      (4 * C + 32 * V * H ^ 2 + 4 * b ^ 4 * n) / n := by
    field_simp
  rw [hlhs, hrhs]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) hn).mpr
  nlinarith
theorem independent_projection_half_degrees_mse
     [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Matrix ι ι ℝ)
    (hsym : Aᵀ = A) (hidem : A * A = A) (hn : 0 < Fintype.card ι)
    (hdegree : (Fintype.card ι : ℝ) / 2 ≤ A.trace)
    (f : ι → ℝ) (ε : ι → Ω → ℝ) (V C₄ H b : ℝ) (hV : 0 ≤ V) (hH : 0 ≤ H)
    (hf : ∀ i, |f i| ≤ H) (he : projectionEnergy (A *ᵥ f) ≤ Fintype.card ι * b ^ 2)
    (hε : ∀ i, MemLp (ε i) 4 μ) (hind : iIndepFun ε μ)
    (hmean : ∀ i, (∫ ω, ε i ω ∂μ) = 0)
    (hsecond : ∀ i, (∫ ω, ε i ω ^ 2 ∂μ) = V)
    (hfourth : ∀ i, (∫ ω, ε i ω ^ 4 ∂μ) ≤ C₄) :
    (∫ ω, (projectionEstimator A (f + fun i => ε i ω) - V) ^ 2 ∂μ) ≤
      (4 * max C₄ (2 * V ^ 2) + 32 * V * H ^ 2) / Fintype.card ι + 4 * b ^ 4 := by
  have hnreal : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hd  := (half_pos hnreal).trans_le hdegree
  have h_independent_projection_estimator_mse_bound : (∫ ω, (projectionEstimator A (f + fun i => ε i ω) - V) ^ 2 ∂μ) ≤
      (2 * max C₄ (2 * V ^ 2) * A.trace + 8 * V * projectionEnergy (A *ᵥ f)) / A.trace ^ 2 +
        (projectionEnergy (A *ᵥ f) / A.trace) ^ 2 := by
    have htwo (i : ι) : MemLp (ε i) 2 μ := (hε i).mono_exponent (by norm_num)
    apply projection_estimator_mse_bound μ A hsym hidem hd f (fun ω i => ε i ω)
      V (max C₄ (2 * V ^ 2)) (fun i => (∫ ω, ε i ω ^ 4 ∂μ) - V ^ 2)
      htwo hmean (projection_coordinate_covariance μ (fun ω i => ε i ω) V htwo hind hmean hsecond)
      (independent_error_product_memLp_two μ ε hε)
      (independent_error_product_covariance μ ε hind hε hmean V hsecond)
    · intro i
      have hf := hfourth i
      have := le_max_left C₄ (2 * V ^ 2)
      nlinarith [sq_nonneg V]
    · exact le_max_right _ _
  apply h_independent_projection_estimator_mse_bound.trans
  have h_projection_energy_le_uniform_bound : projectionEnergy (A *ᵥ f) ≤ Fintype.card ι * H ^ 2 := by
    apply (projection_energy_le A hsym hidem f).trans
    calc
      (∑ i, f i * f i) ≤ ∑ _i : ι, H ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hs := (sq_le_sq₀ (abs_nonneg _) hH).mpr (hf i)
        rw [sq_abs] at hs
        simpa only [pow_two] using hs
      _ = _ := by simp
  exact projection_half_degrees_risk_algebra hnreal hd hdegree
    (projectionEnergy_nonneg _) h_projection_energy_le_uniform_bound he hV
    ((by positivity : 0 ≤ 2 * V ^ 2).trans (le_max_right C₄ (2 * V ^ 2)))
def gridProjectionConstant  (C : ModelConstants d) : ℝ :=
  4 * max C.fourthBound (2 * C.varianceUpper ^ 2) +
    32 * C.varianceUpper * C.holderBound ^ 2
theorem regular_grid_polynomial_residual_bound  
    [Fintype ι] [DecidableEq ι]
    (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
    (k hk) (x : ι → Covariate d) (hx : ∀ i, x i ∈ unitCube d) :
    projectionEnergy
      ((1 - empiricalDesignProjection (cellPolynomialDesign (ℓ := C.order)
        (fun i => regularGridCell k hk (x i)) x)) *ᵥ (fun i => θ.regression (x i))) ≤
      Fintype.card ι * (taylorErrorFactor C * C.holderBound * (1 / k) ^ C.smoothness) ^ 2 := by
  have h_admissible_cell_polynomial_residual_bound {κ} [Fintype κ] [DecidableEq κ] (hθ : Admissible C θ) (cell : ι → κ) (z : κ → Covariate d) (hz : ∀ c, z c ∈ unitCube d) (h : ℝ) (hh : 0 ≤ h) (hradius : ∀ i r, |x i r - z (cell i) r| ≤ h) : projectionEnergy
      ((1 - empiricalDesignProjection (cellPolynomialDesign (ℓ := C.order) cell x)) *ᵥ
        (fun i => θ.regression (x i))) ≤
      Fintype.card ι * (taylorErrorFactor C * C.holderBound * h ^ C.smoothness) ^ 2 := by
    have h_admissible_regression_taylor_cell (x) (hx : x ∈ unitCube d) : ∃ P, P.totalDegree ≤ C.order ∧
        ∀ y ∈ unitCube d, (∀ i, |y i - x i| ≤ h) →
          |θ.regression y - MvPolynomial.eval y P| ≤
            taylorErrorFactor C * C.holderBound * h ^ C.smoothness := by
      rcases hθ with ⟨_, _, _, _, ⟨F, hcube, hreg, hNorm⟩, _, _, _⟩
      refine ⟨modelTaylorPolynomial C F x, modelTaylorPolynomial_degree C F x, ?_⟩
      intro y hy hxy
      simpa only [hcube y hy] using
        modelTaylorPolynomial_cell_error C F hreg hNorm x y hx hy h hh hxy
    choose P hP using fun c => (h_admissible_regression_taylor_cell (z c) (hz c))
    apply cell_polynomial_residual_bound cell x (fun i => θ.regression (x i)) P
      (fun c => (hP c).1) (taylorErrorFactor C * C.holderBound * h ^ C.smoothness)
    · exact mul_nonneg (mul_nonneg (taylorErrorFactor_pos C).le C.holderBound_pos.le)
        (Real.rpow_nonneg hh _)
    · intro i
      exact (hP (cell i)).2 (x i) (hx i) (hradius i)
  apply h_admissible_cell_polynomial_residual_bound hθ (fun i => regularGridCell k hk (x i)) (regularGridCorner k) (regular_grid_corner_mem_cube k hk) (1 / k) (by positivity)
  exact fun i r => regular_grid_cell_radius k hk (x i) (hx i) r
theorem regular_grid_polynomial_residual_degrees  
    [Fintype ι] [DecidableEq ι] (ℓ k hk) (x : ι → Covariate d) :
    (Fintype.card ι : ℝ) - k ^ d * (ℓ + 1 : ℕ) ^ d ≤
      (1 - empiricalDesignProjection (cellPolynomialDesign (ℓ := ℓ)
        (fun i => regularGridCell k hk (x i)) x)).trace := by
  have h_cell_polynomial_residual_degrees {κ} [Fintype κ] [DecidableEq κ] (cell : ι → κ) : (Fintype.card ι : ℝ) - Fintype.card κ * (ℓ + 1 : ℕ) ^ d ≤
      (1 - empiricalDesignProjection (cellPolynomialDesign (ℓ := ℓ) cell x)).trace := by
    simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
      Nat.cast_mul, Nat.cast_pow] using
      empirical_design_residual_degrees (cellPolynomialDesign (ℓ := ℓ) cell x)
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using
    (h_cell_polynomial_residual_degrees (fun i => regularGridCell k hk (x i)))
instance designMatrixMeasurableAdd {ι κ : Type*} : MeasurableAdd₂ (Matrix ι κ ℝ) :=
  inferInstanceAs (MeasurableAdd₂ (ι → κ → ℝ))
instance designMatrixMeasurableSub {ι κ : Type*} : MeasurableSub₂ (Matrix ι κ ℝ) :=
  inferInstanceAs (MeasurableSub₂ (ι → κ → ℝ))
theorem design_measurable_mulVec [MeasurableSpace Ω] [Fintype ι]
    (P : Ω → Matrix ι ι ℝ) (v : Ω → ι → ℝ) (hP : Measurable P) (hv : Measurable v) :
    Measurable (fun x => P x *ᵥ v x) :=
  measurable_pi_iff.mpr fun i => Finset.measurable_sum _ fun j _ =>
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hP)).mul ((measurable_pi_apply j).comp hv)
theorem design_list_projection_measurable [MeasurableSpace Ω] [Fintype ι] (vs : List κ) (v : κ → Ω → ι → ℝ)
    (hv : ∀ j, Measurable (v j)) :
    Measurable (fun x => designListProjection (vs.map (fun j => v j x))) := by
  induction vs with
  | nil => exact measurable_const
  | cons j vs ih =>
    have hr  :=
      (hv j).sub (design_measurable_mulVec _ (v j) ih (hv j))
    exact ih.add ((Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hr).mul ((measurable_pi_apply i).comp hr)).inv.smul
      (measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ((measurable_pi_apply i).comp hr).mul ((measurable_pi_apply j).comp hr)))
def polynomialGridEstimator (C : ModelConstants d) (n k)
    (hk : 0 < k) : Estimator d n :=
  ⟨fun z => projectionEstimator
    (1 - empiricalDesignProjection (cellPolynomialDesign (ℓ := C.order)
      (fun i => regularGridCell k hk (z i).1) (fun i => (z i).1)))
    (fun i => (z i).2), by
    have hcell : Measurable (fun z : Fin n → Observation d => fun i => regularGridCell k hk (z i).1) :=
      measurable_pi_iff.mpr fun i => (regular_grid_cell_measurable k hk).comp (by fun_prop)
    have hB : Measurable (fun z : Fin n → Observation d => cellPolynomialDesign (ℓ := C.order)
        (fun i => regularGridCell k hk (z i).1) (fun i => (z i).1)) :=
      measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
        Measurable.ite (((measurable_pi_apply i).comp hcell) (measurableSet_singleton j.1))
          (Finset.measurable_prod Finset.univ (fun r _ => by fun_prop)) measurable_const
    have hA : Measurable (fun z : Fin n → Observation d => 1 - empiricalDesignProjection
        (cellPolynomialDesign (ℓ := C.order) (fun i => regularGridCell k hk (z i).1) (fun i => (z i).1))) :=
      measurable_const.sub (design_list_projection_measurable Finset.univ.toList _ fun j =>
        measurable_pi_iff.mpr fun i => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hB))
    have hY : Measurable (fun z : Fin n → Observation d => fun i => (z i).2) := by fun_prop
    exact (Finset.measurable_sum Finset.univ fun i _ => ((measurable_pi_apply i).comp hY).mul ((measurable_pi_apply i).comp (design_measurable_mulVec _ _ hA hY))).div
      (Finset.measurable_sum Finset.univ fun i _ => (measurable_pi_apply i).comp ((measurable_pi_apply i).comp hA))⟩
def polynomialGridBias  (C : ModelConstants d) (k : ℕ) : ℝ :=
  4 * (taylorErrorFactor C * C.holderBound * (1 / k) ^ C.smoothness) ^ 4
theorem independent_polynomial_grid_projection_mse_bound
    {d n : ℕ}  [MeasurableSpace Ω]
    (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
    (k : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hcolumns : (k : ℝ) ^ d * (C.order + 1 : ℕ) ^ d ≤ (n : ℝ) / 2)
    (x : Fin n → Covariate d) (hx : ∀ i, x i ∈ unitCube d)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ε : Fin n → Ω → ℝ)
    (hε : ∀ i, MemLp (ε i) 4 μ) (hind : iIndepFun ε μ)
    (hmean : ∀ i, (∫ ω, ε i ω ∂μ) = 0)
    (hsecond : ∀ i, (∫ ω, ε i ω ^ 2 ∂μ) = θ.variance)
    (hfourth : ∀ i, (∫ ω, ε i ω ^ 4 ∂μ) ≤ C.fourthBound) :
    (∫ ω, ((polynomialGridEstimator C n k hk).val
      (fun i => (x i, θ.regression (x i) + ε i ω)) - θ.variance) ^ 2 ∂μ) ≤
      gridProjectionConstant C / n + polynomialGridBias C k := by
  let B := cellPolynomialDesign (ℓ := C.order) (fun i => regularGridCell k hk (x i)) x
  have hP := empirical_design_projection_spec B
  have hA := projection_complement _ hP.1 hP.2.1
  have hdegree : ↑n / 2 ≤ (1 - empiricalDesignProjection B).trace := by
    have hdeg := regular_grid_polynomial_residual_degrees C.order k hk x
    simp only [Fintype.card_fin] at hdeg
    linarith
  have hbound := independent_projection_half_degrees_mse μ _ hA.1 hA.2
    (by simpa using hn) (by simpa using hdegree) (fun i => θ.regression (x i)) ε
    θ.variance C.fourthBound C.holderBound
    (taylorErrorFactor C * C.holderBound * (1 / k) ^ C.smoothness)
    (C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1) C.holderBound_pos.le
    (fun i => admissible_regression_value_bound C θ hθ (x i) (hx i))
    (regular_grid_polynomial_residual_bound C θ hθ k hk x hx)
    hε hind hmean hsecond hfourth
  apply hbound.trans
  have h_admissible_grid_projection_constant_bound : 4 * max C.fourthBound (2 * θ.variance ^ 2) +
      32 * θ.variance * C.holderBound ^ 2 ≤ gridProjectionConstant C := by
    have hV0  := C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1
    have hV  := hθ.2.2.2.2.2.2.1
    have hsq := (sq_le_sq₀ hV0 (hV0.trans hV)).mpr hV
    have := max_le_max_left C.fourthBound (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2))
    have := mul_le_mul_of_nonneg_right hV (by positivity : 0 ≤ 32 * C.holderBound ^ 2)
    unfold gridProjectionConstant
    nlinarith
  have hdiv := div_le_div_of_nonneg_right h_admissible_grid_projection_constant_bound
    (Nat.cast_nonneg n)
  simpa only [Fintype.card_fin, polynomialGridBias] using
    add_le_add hdiv (le_refl (polynomialGridBias C k))
def polynomialFeatureCount  (C : ModelConstants d) : ℕ := (C.order + 1) ^ d
theorem polynomialFeatureCount_pos {d : ℕ} (C : ModelConstants d) :
    0 < polynomialFeatureCount C := by
  unfold polynomialFeatureCount
  positivity
def polynomialProjectionGridSize {d : ℕ} (C : ModelConstants d) (n : ℕ) : ℕ :=
  ⌊((n : ℝ) / (2 * polynomialFeatureCount C)) ^ ((d : ℝ)⁻¹)⌋₊
theorem polynomial_projection_grid_size_spec  (C : ModelConstants d)
    (hn : 2 * polynomialFeatureCount C ≤ n) :
    0 < polynomialProjectionGridSize C n ∧
    (polynomialProjectionGridSize C n : ℝ) ^ d * (C.order + 1 : ℕ) ^ d ≤ ↑n / 2 ∧
    ((n : ℝ) / (2 * polynomialFeatureCount C)) ^ ((d : ℝ)⁻¹) ≤
      2 * polynomialProjectionGridSize C n := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast C.dimension_pos
  have hqreal : (0 : ℝ) < polynomialFeatureCount C := by exact_mod_cast polynomialFeatureCount_pos C
  have hnreal : 2 * (polynomialFeatureCount C : ℝ) ≤ n := by exact_mod_cast hn
  let r := ((n : ℝ) / (2 * polynomialFeatureCount C)) ^ ((d : ℝ)⁻¹)
  have hr1 : 1 ≤ r := Real.one_le_rpow (by apply (le_div_iff₀ (by positivity)).mpr; simpa only [one_mul] using hnreal) (inv_nonneg.mpr hdreal.le)
  have hk : 0 < polynomialProjectionGridSize C n := Nat.floor_pos.mpr hr1
  have hkle : (polynomialProjectionGridSize C n ) ≤ r := Nat.floor_le (by positivity)
  have hroot : r ^ d = n / (2 * polynomialFeatureCount C) :=
    Real.rpow_inv_natCast_pow (by positivity) C.dimension_pos.ne'
  have hbudget := (pow_le_pow_left₀ (Nat.cast_nonneg _) hkle d).trans_eq hroot
  have hbudget' := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * polynomialFeatureCount C)).mp hbudget
  have hfeature : ((C.order + 1 : ℕ) : ℝ) ^ d = polynomialFeatureCount C := by
    simp only [polynomialFeatureCount, Nat.cast_pow]
  have hcolumns : (polynomialProjectionGridSize C n : ℝ) ^ d * (C.order + 1 : ℕ) ^ d ≤ ↑n / 2 := by
    rw [hfeature]
    nlinarith
  have : r < (polynomialProjectionGridSize C n ) + 1 := Nat.lt_floor_add_one r
  have hk1 : (1 : ℝ) ≤ polynomialProjectionGridSize C n := by exact_mod_cast hk
  exact ⟨hk, hcolumns, by linarith⟩
def polynomialProjectionApproximationConstant  (C : ModelConstants d) : ℝ :=
  4 * (taylorErrorFactor C * C.holderBound *
    (2 * (2 * polynomialFeatureCount C : ℝ) ^ ((d : ℝ)⁻¹)) ^ C.smoothness) ^ 4
def projectionUpperConstant  (C : ModelConstants d) : ℝ :=
  gridProjectionConstant C + polynomialProjectionApproximationConstant C +
    2 * polynomialFeatureCount C * (C.varianceUpper - C.varianceLower) ^ 2
def projectionUpperEstimator  (C : ModelConstants d) (n ) : Estimator d n :=
  if hn : 2 * polynomialFeatureCount C ≤ n then
    polynomialGridEstimator C n (polynomialProjectionGridSize C n)
      (polynomial_projection_grid_size_spec C hn).1
  else constantEstimator d n C.varianceLower
theorem paper_parametric {d : ℕ} (C : ModelConstants d) : ParametricClaim C := by
  have h_gridProjectionConstant_nonneg : 0 ≤ gridProjectionConstant C := by
    have : 0 < C.varianceUpper := C.varianceLower_pos.trans C.variance_interval
    have : 0 ≤ max C.fourthBound (2 * C.varianceUpper ^ 2) :=
      (by positivity : 0 ≤ 2 * C.varianceUpper ^ 2).trans (le_max_right _ _)
    unfold gridProjectionConstant
    positivity
  have h_polynomialProjectionApproximationConstant_nonneg : 0 ≤ polynomialProjectionApproximationConstant C := by
    unfold polynomialProjectionApproximationConstant
    positivity
  have h_projectionUpperConstant_nonneg : 0 ≤ projectionUpperConstant C := by
    have := h_gridProjectionConstant_nonneg
    have := h_polynomialProjectionApproximationConstant_nonneg
    unfold projectionUpperConstant
    positivity
  intro hs hparametric
  obtain ⟨c, hc, hlower⟩ := parametric_minimax_lower C
  let A := max (Real.sqrt (2 * projectionUpperConstant C)) (max 1 c⁻¹)
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) ((le_max_left 1 c⁻¹).trans (le_max_right _ _))
  have hAc : A⁻¹ ≤ c := by
    calc
      A⁻¹ ≤ (c⁻¹)⁻¹ := (inv_le_inv₀ hA (inv_pos.mpr hc)).mpr ((le_max_right 1 c⁻¹).trans (le_max_right _ _))
      _ = c := inv_inv c
  refine ⟨A, hA, ?_⟩
  intro n hn
  have hscale := Real.rpow_nonneg (Nat.cast_nonneg n) (-(1 / 2 ))
  constructor
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAc hscale)).trans (hlower n hn)
  have h_minimax_rms_projection_parametric_upper {n : ℕ} (hn : 0 < n) : minimaxRMS C n ≤ ENNReal.ofReal (Real.sqrt (2 * projectionUpperConstant C) *
      (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
    have hdreal : (0 : ℝ) < d := by exact_mod_cast C.dimension_pos
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hexp : -(2 * C.smoothness / d) ≤ -(1 / 2 : ℝ) := by
      apply neg_le_neg
      apply (le_div_iff₀ hdreal).mpr
      nlinarith [hparametric]
    have hp := Real.rpow_le_rpow_of_exponent_le hn1 hexp
    have h_minimax_rms_projection_upper : minimaxRMS C n ≤ ENNReal.ofReal (Real.sqrt (2 * projectionUpperConstant C) *
        max ((n : ℝ) ^ (-(1 / 2 : ℝ))) ((n : ℝ) ^ (-(2 * C.smoothness / d)))) := by
      have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
      have hK := h_projectionUpperConstant_nonneg
      let a := (n : ℝ) ^ (-(1 / 2 : ℝ))
      let b := (n : ℝ) ^ (-(2 * C.smoothness / d))
      let m := max a b
      have ha0 : 0 ≤ a := Real.rpow_nonneg hnreal.le _
      have hb0 : 0 ≤ b := Real.rpow_nonneg hnreal.le _
      have hm0 : 0 ≤ m := ha0.trans (le_max_left a b)
      have ha : a ^ 2 = 1 / (n : ℝ) := by
        dsimp [a]
        rw [← Real.rpow_mul_natCast hnreal.le]
        norm_num
        simp only [Real.rpow_neg_one]
      have hb : b ^ 2 = (n : ℝ) ^ (-(4 * C.smoothness / d)) := by
        dsimp [b]
        rw [← Real.rpow_mul_natCast hnreal.le]
        congr 1
        ring
      have ham : a ^ 2 ≤ m ^ 2 := (sq_le_sq₀ ha0 hm0).mpr (le_max_left a b)
      have hbm : b ^ 2 ≤ m ^ 2 := (sq_le_sq₀ hb0 hm0).mpr (le_max_right a b)
      have hreal : projectionUpperConstant C *
          (1 / (n : ℝ) + (n : ℝ) ^ (-(4 * C.smoothness / d))) ≤
          2 * projectionUpperConstant C * m ^ 2 := by
        rw [← ha, ← hb]
        have hm := mul_le_mul_of_nonneg_left (add_le_add ham hbm) hK
        nlinarith
      have h_projection_upper_estimator_risk : worstCaseRisk C (projectionUpperEstimator C n) ≤
          ENNReal.ofReal (projectionUpperConstant C *
            (1 / (n : ℝ) + (n : ℝ) ^ (-(4 * C.smoothness / d)))) := by
        have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
        have h_projection_upper_constant_bounds : gridProjectionConstant C ≤ projectionUpperConstant C ∧
          polynomialProjectionApproximationConstant C ≤ projectionUpperConstant C ∧
          2 * polynomialFeatureCount C * (C.varianceUpper - C.varianceLower) ^ 2 ≤
            projectionUpperConstant C := by
          have hg := h_gridProjectionConstant_nonneg
          have ha := h_polynomialProjectionApproximationConstant_nonneg
          have hf : 0 ≤ 2 * (polynomialFeatureCount C : ℝ) * (C.varianceUpper - C.varianceLower) ^ 2 := by positivity
          unfold projectionUpperConstant
          constructor
          · linarith
          constructor <;> linarith
        have hbounds := h_projection_upper_constant_bounds
        have hK := h_projectionUpperConstant_nonneg
        by_cases hbudget : 2 * polynomialFeatureCount C ≤ n
        · rw [projectionUpperEstimator, dite_eq_left hbudget]
          have hspec := polynomial_projection_grid_size_spec C hbudget
          have h_polynomial_grid_worst_case_risk_bound : worstCaseRisk C (polynomialGridEstimator C n (polynomialProjectionGridSize C n) hspec.1) ≤
        ENNReal.ofReal (gridProjectionConstant C / n + polynomialGridBias C (polynomialProjectionGridSize C n)) := by
            have h_polynomial_grid_sample_risk_bound {n : ℕ} (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) (hn : 0 < n) (hcolumns : (k : ℝ) ^ d * (C.order + 1 : ℕ) ^ d ≤ (n : ℝ) / 2) : meanSquaredRisk (polynomialGridEstimator C n k hk) θ ≤
                ENNReal.ofReal (gridProjectionConstant C / n + polynomialGridBias C k) := by
              letI := designLaw_isProbability C θ hθ
              letI : IsProbabilityMeasure (designVectorLaw θ n) :=
                inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => designLaw θ)))
              have h_meanSquaredRisk_conditioning (T : Estimator d n) : meanSquaredRisk T θ =
                  ∫⁻ x, ∫⁻ u, ENNReal.ofReal
                    ((T.val (samplesFromDesignErrors θ (x, u)) - θ.variance) ^ 2)
                    ∂conditionalErrorLaw θ x ∂designVectorLaw θ n := by
                have h_sampleLaw_lintegral_conditioning (g : (Fin n → Observation d) → ℝ≥0∞) (hg : Measurable g) : (∫⁻ z, g z ∂sampleLaw θ n) =
                    ∫⁻ x, ∫⁻ u, g (samplesFromDesignErrors θ (x, u))
                      ∂conditionalErrorLaw θ x ∂designVectorLaw θ n := by
                  let := designLaw_isProbability C θ hθ
                  let : IsProbabilityMeasure (designVectorLaw θ n) :=
                    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ => designLaw θ)))
                  have hgm : Measurable (fun z : (Fin n → Covariate d) × (Fin n → ℝ) =>
                      g (samplesFromDesignErrors θ z)) :=
                    hg.comp (samplesFromDesignErrors_measurable θ hθ.2.1)
                  rw [sampleLaw_eq_conditional_map C θ hθ,
                    lintegral_map' hg.aemeasurable (samplesFromDesignErrors_measurable θ hθ.2.1).aemeasurable,
                    Measure.lintegral_compProd hgm]
                  rfl
                apply h_sampleLaw_lintegral_conditioning
                exact ENNReal.measurable_ofReal.comp ((T.property.sub measurable_const).pow_const 2)
              rw [(h_meanSquaredRisk_conditioning _)]
              have hconditional : ∀ᵐ x ∂designVectorLaw θ n,
                  (∫⁻ u, ENNReal.ofReal
                    (((polynomialGridEstimator C n k hk).val (samplesFromDesignErrors θ (x, u)) - θ.variance) ^ 2)
                    ∂conditionalErrorLaw θ x) ≤
                  ENNReal.ofReal (gridProjectionConstant C / n + polynomialGridBias C k) := by
                have h_admissible_conditional_error_facts : ∀ᵐ x ∂designVectorLaw θ n,
                  (∀ i, x i ∈ unitCube d) ∧
                  (∀ i, MemLp (fun u : Fin n → ℝ => u i) 4 (conditionalErrorLaw θ x)) ∧
                  iIndepFun (fun i (u : Fin n → ℝ) => u i) (conditionalErrorLaw θ x) ∧
                  (∀ i, (∫ u, u i ∂conditionalErrorLaw θ x) = 0) ∧
                  (∀ i, (∫ u, (u i) ^ 2 ∂conditionalErrorLaw θ x) = θ.variance) ∧
                  (∀ i, (∫ u, (u i) ^ 4 ∂conditionalErrorLaw θ x) ≤ C.fourthBound) := by
                  let := designLaw_isProbability C θ hθ
                  have hgood : ∀ᵐ x ∂designVectorLaw θ n, ∀ i,
                      x i ∈ unitCube d ∧
                      Integrable (fun u => u) (θ.errors (x i)) ∧
                      Integrable (fun u => u ^ 2) (θ.errors (x i)) ∧
                      Integrable (fun u => u ^ 4) (θ.errors (x i)) ∧
                      (∫ u : ℝ, u ∂θ.errors (x i)) = 0 ∧
                      (∫ u : ℝ, u ^ 2 ∂θ.errors (x i)) = θ.variance ∧
                      (∫ u : ℝ, u ^ 4 ∂θ.errors (x i)) ≤ C.fourthBound := by
                    apply eventually_all.mpr
                    intro i
                    exact (Measure.tendsto_eval_ae_ae (μ := fun _ => designLaw θ) (i := i)).eventually ((designLaw_cube_ae θ).and hθ.2.2.2.2.2.2.2)
                  filter_upwards [hgood] with x hx
                  have h_conditionalErrorLaw_iIndepFun  := iIndepFun_pi (μ := fun i => θ.errors (x i)) (X := fun _ => id)
                    (fun _ => aemeasurable_id)
                  refine ⟨fun i => (hx i).1, ?_, h_conditionalErrorLaw_iIndepFun, ?_, ?_, ?_⟩
                  · intro i
                    have h_memLp_id_four_of_integrable_fourth : MemLp (fun u => u) 4 (θ.errors (x i)) := by
                      apply (integrable_norm_rpow_iff (f := fun u => u) (p := 4)
                        aestronglyMeasurable_id (by norm_num) (by simp)).mp
                      have heq : (fun u : ℝ => ‖u‖ ^ ((4 : ℝ≥0∞).toReal)) = (fun u => u ^ 4) := by
                        funext u
                        norm_num only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
                        calc
                          |u| ^ (4 : ℝ) = |u| ^ (4 : ℕ) := Real.rpow_natCast _ _
                          _ = |u ^ 4| := (abs_pow u 4).symm
                          _ = u ^ 4 := abs_of_nonneg (by positivity)
                      rw [heq]
                      exact ((hx i).2.2.2.1)
                    simpa only [Function.comp_def, Function.eval, conditionalErrorLaw] using
                      h_memLp_id_four_of_integrable_fourth.comp_measurePreserving
                        (measurePreserving_eval (fun j => θ.errors (x j)) i)
                  · intro i
                    rw [conditionalErrorLaw_integral_coordinate θ x i (fun u => u) measurable_id]
                    exact (hx i).2.2.2.2.1
                  · intro i
                    rw [conditionalErrorLaw_integral_coordinate θ x i (fun u => u ^ 2) (by fun_prop)]
                    exact (hx i).2.2.2.2.2.1
                  · intro i
                    rw [conditionalErrorLaw_integral_coordinate θ x i (fun u => u ^ 4) (by fun_prop)]
                    exact (hx i).2.2.2.2.2.2
                filter_upwards [h_admissible_conditional_error_facts] with x hx
                obtain ⟨hcube, hε, hind, hmean, hsecond, hfourth⟩ := hx
                let B := cellPolynomialDesign (ℓ := C.order) (fun i => regularGridCell k hk (x i)) x
                let A := 1 - empiricalDesignProjection B
                let f := fun i => θ.regression (x i)
                have hP := empirical_design_projection_spec B
                have hA := projection_complement _ hP.1 hP.2.1
                have hX := projection_estimator_memLp_two (conditionalErrorLaw θ x) A hA.1 f (fun ω i => (fun i u => u i) i ω)
                  (fun i => (hε i).mono_exponent (by norm_num))
                  (independent_error_product_memLp_two (conditionalErrorLaw θ x) (fun i u => u i) hε)
                have hsq : Integrable
                    (fun ω => (projectionEstimator A (f + fun i => (fun i u => u i) i ω) - θ.variance) ^ 2) (conditionalErrorLaw θ x) := by
                  simpa only [Real.norm_eq_abs, sq_abs, Pi.sub_apply] using
                    (hX.sub (memLp_const θ.variance)).integrable_norm_pow (by norm_num : ↑2 ≠ 0)
                have hbound := independent_polynomial_grid_projection_mse_bound C θ hθ k hk hn hcolumns
                  x hcube (conditionalErrorLaw θ x) (fun i u => u i) hε hind hmean hsecond hfourth
                change (∫⁻ ω, ENNReal.ofReal
                  ((projectionEstimator A (f + fun i => (fun i u => u i) i ω) - θ.variance) ^ 2) ∂(conditionalErrorLaw θ x)) ≤ _
                rw [← ofReal_integral_eq_lintegral_ofReal hsq (Filter.Eventually.of_forall (fun ω => sq_nonneg _))]
                exact ENNReal.ofReal_le_ofReal hbound
              exact (lintegral_mono_ae hconditional).trans_eq (by simp)
            exact iSup_le fun θ => (h_polynomial_grid_sample_risk_bound θ.val θ.property (polynomialProjectionGridSize C n) hspec.1 hn hspec.2.1)
          have hbase := h_polynomial_grid_worst_case_risk_bound
          apply hbase.trans
          apply ENNReal.ofReal_le_ofReal
          have h_polynomial_projection_grid_bias_rate : polynomialGridBias C (polynomialProjectionGridSize C n) ≤
        polynomialProjectionApproximationConstant C * (n : ℝ) ^ (-(4 * C.smoothness / d)) := by
            have hnreal : (0 : ℝ) < n := by
              exact_mod_cast (lt_of_lt_of_le (by have := polynomialFeatureCount_pos C; omega : 0 < 2 * polynomialFeatureCount C) hbudget)
            have hkreal : (0 : ℝ) < polynomialProjectionGridSize C n := by
              exact_mod_cast (polynomial_projection_grid_size_spec C hbudget).1
            have h_polynomial_projection_grid_inverse_width_bound : 1 / (polynomialProjectionGridSize C n : ℝ) ≤
                (2 * (2 * polynomialFeatureCount C : ℝ) ^ ((d : ℝ)⁻¹)) *
                  (n : ℝ) ^ (-((d : ℝ)⁻¹)) := by
              have hqreal : (0 : ℝ) < polynomialFeatureCount C := by exact_mod_cast polynomialFeatureCount_pos C
              have hnreal : (0 : ℝ) < n := by
                exact_mod_cast (lt_of_lt_of_le (by have := polynomialFeatureCount_pos C; omega : 0 < 2 * polynomialFeatureCount C) hbudget)
              have hspec := polynomial_projection_grid_size_spec C hbudget
              have hkreal : (0 : ℝ) < polynomialProjectionGridSize C n := by exact_mod_cast hspec.1
              have hrreal : (0 : ℝ) < ((n : ℝ) / (2 * polynomialFeatureCount C)) ^ ((d : ℝ)⁻¹) :=
                Real.rpow_pos_of_pos (by positivity) _
              have hi : 1 / (polynomialProjectionGridSize C n : ℝ) ≤
                  2 / (((n : ℝ) / (2 * polynomialFeatureCount C)) ^ ((d : ℝ)⁻¹)) := by
                apply (div_le_div_iff₀ hkreal hrreal).mpr
                simpa only [one_mul] using hspec.2.2
              apply hi.trans_eq
              rw [Real.div_rpow hnreal.le (by positivity), Real.rpow_neg hnreal.le]
              field_simp
            have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1 / (polynomialProjectionGridSize C n : ℝ))
              h_polynomial_projection_grid_inverse_width_bound C.smoothness_pos.le
            have hcoef : 0 ≤ taylorErrorFactor C * C.holderBound :=
              mul_nonneg (taylorErrorFactor_pos C).le C.holderBound_pos.le
            have hpow := pow_le_pow_left₀ (mul_nonneg hcoef (Real.rpow_nonneg (by positivity) _)) (mul_le_mul_of_nonneg_left hp hcoef) 4
            unfold polynomialGridBias polynomialProjectionApproximationConstant
            apply (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 4)).trans_eq
            rw [Real.mul_rpow (by positivity) (by positivity)]
            have hpower : (((n : ℝ) ^ (-((d : ℝ)⁻¹))) ^ C.smoothness) ^ 4 =
                (n : ℝ) ^ (-(4 * C.smoothness / d)) := by
              rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (by positivity), ← Real.rpow_mul hnreal.le]
              congr 1
              ring
            simp only [mul_pow]
            rw [hpower]
            ring
          have hb := h_polynomial_projection_grid_bias_rate
          have hG := mul_le_mul_of_nonneg_right hbounds.1 (by positivity : 0 ≤ (n : ℝ)⁻¹)
          have hA := mul_le_mul_of_nonneg_right hbounds.2.1
            (Real.rpow_nonneg hnreal.le (-(4 * C.smoothness / d)))
          calc
            _ ≤ gridProjectionConstant C / n + polynomialProjectionApproximationConstant C *
                (n : ℝ) ^ (-(4 * C.smoothness / d)) := add_le_add le_rfl hb
            _ ≤ projectionUpperConstant C / n + projectionUpperConstant C *
                (n : ℝ) ^ (-(4 * C.smoothness / d)) :=
              add_le_add (div_le_div_of_nonneg_right hbounds.1 (Nat.cast_nonneg n)) hA
            _ = _ := by ring
        · rw [projectionUpperEstimator, dite_eq_right hbudget]
          apply iSup_le
          intro θ
          apply (constantEstimator_risk_bound C θ.val θ.property).trans
          apply ENNReal.ofReal_le_ofReal
          have hsmall : (n : ℝ) ≤ 2 * polynomialFeatureCount C := by
            exact_mod_cast (by omega : n ≤ 2 * polynomialFeatureCount C)
          have hdiam : (C.varianceUpper - C.varianceLower) ^ 2 ≤ projectionUpperConstant C / n := by
            apply (le_div_iff₀ hnreal).mpr
            have hm := mul_le_mul_of_nonneg_left hsmall (sq_nonneg (C.varianceUpper - C.varianceLower))
            nlinarith [hbounds.2.2]
          have hrate : 0 ≤ (n : ℝ) ^ (-(4 * C.smoothness / d)) := Real.rpow_nonneg hnreal.le _
          calc
            _ ≤ projectionUpperConstant C / n := hdiam
            _ ≤ _ := by rw [div_eq_mul_inv, one_div]; nlinarith [mul_nonneg hK hrate]
      have h_minimax_projection_upper  := (minimaxRisk_le_worstCaseRisk C _).trans h_projection_upper_estimator_risk
      have hMSE := h_minimax_projection_upper.trans (ENNReal.ofReal_le_ofReal hreal)
      apply (ENNReal.rpow_le_rpow hMSE (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ 2 * projectionUpperConstant C * m ^ 2) (by norm_num)]
      congr 1
      rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity : 0 ≤ 2 * projectionUpperConstant C),
        Real.sqrt_sq hm0]
    simpa only [max_eq_left hp] using h_minimax_rms_projection_upper
  · exact (h_minimax_rms_projection_parametric_upper (by omega)).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hscale))
end NearlyMinimax
