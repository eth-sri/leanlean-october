module

public import NearlyMinimax.CellPolynomialProjection
public import NearlyMinimax.GridProjection
public import NearlyMinimax.HolderTaylorBridge
public import NearlyMinimax.ProjectionStatistical
public import RoughRegime.Macro
public import RoughRegime.Notation


@[expose] public section

open Matrix MeasureTheory ProbabilityTheory MvPolynomial
𝚳

noncomputable section
𝚨

𝗇 𝔅 fun i => θ.regression $ x i
𝗇 𝔊 ∀ i, x i ∈ unitCube d
𝗇 𝔑 𝙷₂ * h ^ C.smoothness
𝗇 𝔗 𝙟
𝗇 𝔙 cellPolynomialDesign (ℓ := C.order)
𝗃 𝔛 ἀ C θ hθ
/-- The original admissibility norm supplies a genuine cellwise Taylor
approximation, which the actual polynomial design fits exactly. -/
theorem admissible_cell_polynomial_residual_bound
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (C : ModelConstants d) θ (hθ : 𝔗)
    (cell : ι → κ) x (z : κ → Covariate d)
    (hx : 𝔊) (hz : ∀ c, z c ∈ unitCube d)
    h (hh : 0 ≤ h) (hradius : ∀ i r, |x i r - z (cell i) r| ≤ h) :
    projectionEnergy
      ((1 - empiricalDesignProjection (𝔙 cell x)) *ᵥ
        𝔅) ≤
      Fintype.card ι * 𝔑 ^ 2 := by
  classical
  choose P hP using fun c => 𝔛 admissible_regression_taylor_cell (z c) (hz c) h hh
  apply cell_polynomial_residual_bound cell x 𝔅 P
    (fun c => (hP c).1) 𝔑
  · exact mul_nonneg (mul_nonneg (taylorErrorFactor_pos C).le C.holderBound_pos.le)
      $ Real.rpow_nonneg hh _
  · simp_all

𝗇 𝔄 fun i => 𝘯 $ x i
𝗇 𝔚 𝚖₂
𝗇 𝔈 𝙷₂ * 𝔚 ^ C.smoothness
𝗇 𝔔 𝔙 𝔄 x
/-- Actual regular-grid polynomial fitting proves the approximation
bound in every smoothness order of the original model. -/
theorem regular_grid_polynomial_residual_bound
    [Fintype ι] [DecidableEq ι]
    (C : ModelConstants d) θ (hθ : 𝔗)
    k hk (x : ι → Covariate d) (hx : 𝔊) :
    projectionEnergy
      ((1 - empiricalDesignProjection 𝔔) *ᵥ 𝔅) ≤
      Fintype.card ι * 𝔈 ^ 2 := by
  apply 𝔛 admissible_cell_polynomial_residual_bound
    𝔄 x (regularGridCorner k) hx
    (regular_grid_corner_mem_cube k hk) 𝔚 𝖠₃
  exact fun i r => regular_grid_cell_radius k hk (x i) (hx i) r

𝗇 𝔘 𝖰
/-- The higher-order regular-grid fit leaves sample size minus its
actual rectangular feature count as residual degrees of freedom. -/
theorem regular_grid_polynomial_residual_degrees
    [Fintype ι] [DecidableEq ι] (ℓ k : ℕ) (hk : 𝔘) (x : ι → Covariate d) :
     Fintype.card ι - 𝗋 * (ℓ + 1 : ℕ) ^ d ≤
      (1 - empiricalDesignProjection (cellPolynomialDesign (ℓ := ℓ)
        𝔄 x)).trace := by
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using
    cell_polynomial_residual_degrees 𝔄 x

/-- A genuine Borel higher-order projection estimator on the original
sample space. Features are explicit monomials of observed covariates. -/
def polynomialGridEstimator (C : ModelConstants d) (n k : ℕ)
    (hk : 𝔘) : 𝚠 :=
  ⟨fun z => projectionEstimator
    (1 - empiricalDesignProjection (𝔙
      (fun i => 𝘯 𝚄₁) fun i => 𝚄₁ ))
     fun i => (z i).2 , by
    apply empirical_residual_estimator_measurable
    · apply cell_polynomial_design_measurable
      · apply measurable_pi_iff.mpr
        intro i
        exact (regular_grid_cell_measurable k hk).comp 𝖦₃
      · fun_prop
    · fun_prop⟩

/-- The full-smoothness Taylor bias contribution. -/
def polynomialGridBias (C : ModelConstants d) (k : ℕ) : ℝ :=
  4 * 𝔈 ^ 4

𝗇 𝔖 ε i ω
𝗇 𝔇 ((polynomialGridEstimator C n k hk).val (fun i => (x i, θ.regression (x i) + 𝔖)) - θ.variance) ^ 2
𝗇 𝔉 𝙦 ^ d * (𝗈₂ : ℕ) ^ d ≤ 𝙒 / 2
𝗇 𝔎 ∀ i, ∫ ω, 𝔖 ^ 2 ∂μ = θ.variance
𝗇 𝔏 ∀ i, ∫ ω, 𝔖 ^ 4 ∂μ ≤ C.fourthBound
𝗃 𝔞 ∫ ω, ἀ ∂μ
𝗇 𝔐 ∀ i, 𝔞 𝔖 = 0
𝗇 𝔒 𝗜₂
𝗇 𝔓 gridProjectionConstant C / n + polynomialGridBias C k
/-- The conditional full-smoothness projection MSE is proved from the
original Hölder model, explicit features, and actual independent moments. -/
theorem independent_polynomial_grid_projection_mse_bound
    {d n : ℕ} {Ω } [MeasurableSpace Ω]
    (C : ModelConstants d) (θ : RegressionParameter d) (hθ : 𝔗)
    (k : ℕ) (hk : 𝔘) (hn : 𝗧₁)
    (hcolumns : 𝔉)
    (x : 𝙇) (hx : 𝔊)
    (μ : Measure Ω) [IsProbabilityMeasure μ] ε
    (hε : 𝔒) (hind : iIndepFun ε μ)
    (hmean : 𝔐)
    (hsecond : 𝔎)
    (hfourth : 𝔏) :
    𝔞 𝔇 ≤
      𝔓 := by
  let B := 𝔔
  have hP := empirical_design_projection_spec B
  have hA := projection_complement _ hP.1 hP.2.1
  have hdegree : n / 2 ≤ (1 - empiricalDesignProjection B).trace := by
    have hdeg := regular_grid_polynomial_residual_degrees C.order k hk x
    simp only [Fintype.card_fin] at hdeg
    linarith
  have hbound := independent_projection_half_degrees_mse μ _ hA.1 hA.2
    (by simpa using hn) (by simpa using hdegree) 𝔅 ε
    θ.variance C.fourthBound C.holderBound
    𝔈
    (C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1) C.holderBound_pos.le
    (fun i => 𝔛 admissible_regression_value_bound (x i) $ hx i )
    (𝔛 regular_grid_polynomial_residual_bound k hk x hx)
    hε hind hmean hsecond hfourth
  apply hbound.trans
  have hdiv := div_le_div_of_nonneg_right 𝔛 admissible_grid_projection_constant_bound
    $ Nat.cast_nonneg n
  simpa only [Fintype.card_fin, polynomialGridBias] using
    add_le_add hdiv $ le_refl $ polynomialGridBias C k


𝗇 𝔍 (projectionEstimator A (f + fun i => 𝔖) - θ.variance) ^ 2
𝗃 𝔜 ∫⁻ ω, ENNReal.ofReal ἀ ∂μ
/-- The full-smoothness conditional MSE bound in the extended-real loss
of the actual statistical model, with integrability derived from fourth moments. -/
theorem polynomial_grid_conditional_lintegral_bound
    {d n : ℕ} {Ω } [MeasurableSpace Ω]
    (C : ModelConstants d) (θ : RegressionParameter d) (hθ : 𝔗)
    (k : ℕ) (hk : 𝔘) (hn : 𝗧₁)
    (hcolumns : 𝔉)
    (x : 𝙇) (hx : 𝔊)
    (μ : Measure Ω) [IsProbabilityMeasure μ] ε
    (hε : 𝔒) (hind : iIndepFun ε μ)
    (hmean : 𝔐)
    (hsecond : 𝔎)
    (hfourth : 𝔏) :
    𝔜 𝔇 ≤
      ENNReal.ofReal 𝔓 := by
  let B := 𝔔
  let A := 1 - empiricalDesignProjection B
  let f := 𝔅
  have hP := empirical_design_projection_spec B
  have hX := projection_estimator_memLp_two μ A (projection_complement _ hP.1 hP.2.1).1 f (fun ω i => 𝔖)
    (fun i => (hε i).mono_exponent 𝖠₄ )
    $ independent_error_product_memLp_two μ ε hε
  have hsq : Integrable
      (fun ω => 𝔍) μ := by
    simpa only [Real.norm_eq_abs, sq_abs, Pi.sub_apply] using
      (hX.sub $ memLp_const θ.variance ).integrable_norm_pow 𝖠₄
  have hbound := 𝔛 independent_polynomial_grid_projection_mse_bound k hk hn hcolumns
    x hx μ ε hε hind hmean hsecond hfourth
  change 𝔜 𝔍 ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal hsq $ Filter.Eventually.of_forall fun ω => sq_nonneg _ ]
  exact ENNReal.ofReal_le_ofReal hbound
