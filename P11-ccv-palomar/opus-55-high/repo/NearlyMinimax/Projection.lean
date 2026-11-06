module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation

@[expose] public section

/-!
# Residual projection algebra

The deterministic matrix identities and expectation calculation behind
Lemma `projection-upper`. These statements permit rank deficient design
matrices: only the symmetric idempotent residual matrix is required.
-/

open Matrix MeasureTheory ProbabilityTheory

noncomputable section

𝚨


𝗇 𝔍 𝙛
/-- Squared Euclidean length, independent of the sup norm on function spaces. -/
def projectionEnergy [Fintype ι] (x : 𝔍) : ℝ := x ⬝ᵥ x

𝗇 𝔚 Matrix ι ι ℝ
𝗃 𝕯 A *ᵥ ἀ
/-- The residual quadratic numerator. -/
def projectionQuadratic [Fintype ι] (A : 𝔚) (x : 𝔍) : ℝ :=
  x ⬝ᵥ 𝕯 x

/-- The residual variance estimator before clipping. -/
def projectionEstimator [Fintype ι] (A : 𝔚) (x : 𝔍) : ℝ :=
  projectionQuadratic A x / A.trace

𝗇 𝔅 𝕯 f
𝗃 𝕵 ε ω ἀ
𝗇 𝔧 𝕵 i
𝗇 𝔴 i = j
𝗇 𝔇 ∀ i j, ∫ ω, 𝔧 * 𝕵 j ∂μ = if 𝔴 then V else 0
𝗃 𝕰 fun ω => ἀ
𝗇 𝔈 ∀ i, MemLp 𝕰 𝔧 2 μ
𝗃 𝕬 ∫ ω, ἀ ∂μ
𝗇 𝔊 ∀ i, 𝕬 𝔧 = 0
𝗇 𝔎 fun ω => projectionQuadratic A $ ε ω
𝗇 𝔏 A * A = A
𝗇 𝔐 projectionEstimator A $ f + ε ω
𝗇 𝔑 Aᵀ = A
𝗇 𝔒 𝘩
𝗇 𝔓 projectionQuadratic A $ ε ω
𝗇 𝔔 projectionQuadratic A f
𝗇 𝔢 congrArg (fun M => M i j) hsym
𝗇 𝔣 𝔅 ⬝ᵥ ε ω
𝗇 𝔥 Ω → 𝔍
𝗇 𝔬 𝕰 𝔣
𝗇 𝔮 projection_linear_noise_expectation μ 𝔅 ε hε hmean
𝗇 𝔰 projection_quadratic_add A hsym f
𝗇 𝔶 2 * 𝔣
𝗃 𝕭 ∫ ω, ἀ ^ 2 ∂μ
𝗃 𝕱 ἀ ^ 2
𝗃 𝕲 ἀ A hsym hidem
𝗃 𝕶 (ἀ 𝔔).add $ hlin.const_mul 2
section

variable [Fintype ι]

theorem projectionEnergy_nonneg (x : 𝔍) :
    0 ≤ projectionEnergy x := Finset.sum_nonneg fun i _ => mul_self_nonneg $ x i

𝗇 𝔩 ∑ i, ∑ j, 𝕱 𝔒
/-- The Frobenius square of a symmetric projection equals its trace. -/
theorem projection_sum_squares_eq_trace (A : 𝔚) (hsym : 𝔑) (hidem : 𝔏) :
    𝔩 = A.trace := by
  calc
    𝔩 = (A * A).trace := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hs : A j i = 𝔒 := 𝔢
      grind
    _ = A.trace := 𝖤₄

/-- For a symmetric idempotent matrix, the quadratic form is precisely
the residual's squared Euclidean length. -/
theorem projection_quadratic_eq_energy A (hsym : 𝔑) (hidem : 𝔏) (f : 𝔍) :
    𝔔 = projectionEnergy 𝔅 := by
  unfold projectionQuadratic projectionEnergy
  symm
  rw [dotProduct_mulVec, ← mulVec_transpose, hsym, mulVec_mulVec, hidem, dotProduct_comm]

𝗇 𝔦 f - 𝔅
/-- The residual and fitted components are orthogonal. -/
theorem projection_orthogonal A (hsym : 𝔑) (hidem : 𝔏) (f : 𝔍) :
    𝔅 ⬝ᵥ 𝔦 = 0 := by
  rw [dotProduct_sub]
  have h := 𝕲 projection_quadratic_eq_energy f
  unfold projectionQuadratic projectionEnergy at h
  rw [dotProduct_comm 𝔅 f, h, sub_self]

/-- A symmetric projection cannot increase Euclidean length. -/
theorem projection_energy_le A (hsym : 𝔑) (hidem : 𝔏) (f : 𝔍) :
    projectionEnergy 𝔅 ≤ projectionEnergy f := by
  have horth := 𝕲 projection_orthogonal f
  have hpos := projectionEnergy_nonneg 𝔦
  have hdecomp : projectionEnergy f = projectionEnergy 𝔅 +
      projectionEnergy 𝔦 := by
    have hid : f = 𝔅 + 𝔦 := by abel
    conv_lhs => rw [hid]
    unfold projectionEnergy
    rw [dotProduct_add, add_dotProduct, add_dotProduct, horth,
      dotProduct_comm 𝔦 𝔅, horth]
    ring
  linarith

𝗇 𝔖 f - q
/-- Any candidate fitted vector killed by the residual projection gives
an upper bound for the residual approximation error. -/
theorem projection_residual_minimality A (hsym : 𝔑) (hidem : 𝔏)
    (f q : 𝔍) (hq : 𝕯 q = 0) :
    projectionEnergy 𝔅 ≤ projectionEnergy 𝔖 := by
  have hAq : 𝕯 𝔖 = 𝔅 := by rw [mulVec_sub, hq, sub_zero]
  rw [← hAq]
  exact 𝕲 projection_energy_le 𝔖

/-- A pointwise polynomial approximation of size `b` bounds the total
residual squared error by the sample size multiplied by `b²`. -/
theorem projection_approximation_bound A (hsym : 𝔑) (hidem : 𝔏)
    (f q : 𝔍) (hq : 𝕯 q = 0) b (hb : 𝘸)
    (happrox : ∀ i, |f i - q i| ≤ b) :
    projectionEnergy 𝔅 ≤ Fintype.card ι * 𝕱 b := by
  apply (𝕲 projection_residual_minimality f q hq).trans
  calc
     ∑ i, 𝔖 i * 𝔖 i ≤ ∑ _i : ι, 𝕱 b := by
      apply Finset.sum_le_sum
      intro i hi
      have hs := (𝘉 hb).mpr $ happrox i
      rw [sq_abs] at hs
      simpa only [Pi.sub_apply, pow_two] using hs
    𝘿 := 𝖢₄

/-- Quadratic expansion separates approximation bias, the linear noise
term, and the centered noise quadratic form. -/
theorem projection_quadratic_add A (hsym : 𝔑) (f ε : 𝔍) :
    projectionQuadratic A (f + ε) = 𝔔 +
      2 * 𝔅 ⬝ᵥ ε + projectionQuadratic A ε := by
  unfold projectionQuadratic
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct]
  have hcross : f ⬝ᵥ 𝕯 ε = 𝔅 ⬝ᵥ ε := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym]
  rw [hcross, dotProduct_comm ε 𝔅]
  ring

/-- Entrywise expansion of the actual quadratic form. -/
theorem projection_quadratic_sum A (x : 𝔍) :
    projectionQuadratic A x = ∑ i, ∑ j, 𝔒 * x i * x j := by
  unfold projectionQuadratic mulVec dotProduct
  simp_rw [Finset.mul_sum]
  grind

𝗇 𝔡 ((hε i).integrable_mul $ hε j ).const_mul
/-- Finite quadratic noise forms are integrable under coordinate `L²` bounds. -/
theorem projection_quadratic_integrable [MeasurableSpace Ω] (μ : Measure Ω) A (ε : 𝔥)
    (hε : 𝔈) :
    Integrable 𝔎 μ := by
  simp_rw [projection_quadratic_sum]
  apply integrable_finset_sum
  intro i hi
  apply integrable_finset_sum
  intro j hj
  convert 𝔡 𝔒 using 1
  funext ω
  simp [mul_assoc]

/-- The expected noise quadratic form is variance times trace. The
hypothesis gives ordinary coordinate second moments, not a conclusion
about the quadratic form. -/
theorem projection_noise_expectation [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) A (ε : 𝔥)
    V (hε : 𝔈)
    (hcov : 𝔇) :
    𝕬 𝔓 = V * A.trace := by
  have hij i j : Integrable (fun ω => 𝔒 * 𝔧 * 𝕵 j) μ := by
    convert 𝔡 𝔒 using 1
    funext ω
    simp [mul_assoc]
  simp_rw [projection_quadratic_sum]
  rw [integral_finset_sum Finset.univ fun i _ => integrable_finset_sum _ fun j _ => hij i j ]
  simp_rw [integral_finset_sum Finset.univ fun j _ => hij _ j , mul_assoc,
    integral_const_mul, hcov, mul_ite, mul_zero]
  simp
  unfold trace diag
  rw [Finset.mul_sum]
  grind

𝗇 𝔯 x ⬝ᵥ ε ω
/-- Centered coordinate noise has zero expectation in every linear form. -/
theorem projection_linear_noise_expectation [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    x (ε : 𝔥)
    (hε : 𝔈)
    (hmean : 𝔊) :
    𝕬 𝔯 = 0 := by
  unfold dotProduct
  rw [integral_finset_sum Finset.univ fun i _ =>
    ((hε i).integrable 𝖠₄ ).const_mul $ x i ]
  simp_rw [integral_const_mul, hmean, mul_zero]
  simp

/-- The residual estimator's conditional expectation is variance plus
squared approximation residual divided by the degrees of freedom. -/
theorem projection_estimator_expectation [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    A (hsym : 𝔑) (hidem : 𝔏)
    (hd : A.trace ≠ 0) f (ε : 𝔥) V
    (hε : 𝔈)
    (hmean : 𝔊)
    (hcov : 𝔇) :
    𝕬 𝔐 =
      V + projectionEnergy 𝔅 / A.trace := by
  have hlin : Integrable 𝔬 μ := by
    apply integrable_finset_sum
    intro i hi
    exact ((hε i).integrable 𝖠₄ ).const_mul $ 𝔅 i
  have hsum : Integrable (fun ω => 𝔔 + 𝔶) μ :=
    𝕶 integrable_const
  simp_rw [projectionEstimator, 𝔰]
  rw [integral_div, integral_add hsum $ projection_quadratic_integrable μ A ε hε ,
    integral_add (integrable_const 𝔔) $ hlin.const_mul 2 , integral_const,
    probReal_univ, one_smul, integral_const_mul,
    𝔮,
    mul_zero, add_zero, projection_noise_expectation μ A ε V hε hcov,
    𝕲 projection_quadratic_eq_energy f]
  field_simp
  ring

/-- Independence and centered errors imply the coordinate covariance
identities used by the quadratic expectation theorem. -/
theorem projection_coordinate_covariance [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ε : 𝔥) V
    (hε : 𝔈)
    (hind : iIndepFun (fun i ω => 𝔧) μ)
    (hmean : 𝔊)
    (hsecond : ∀ i, 𝕭 𝔧 = V) :
    𝔇 := by
  intro i j
  by_cases hij : 𝔴
  · subst j
    simp only [← pow_two]
    exact hsecond i
  · have hi := (hind.indepFun hij).integral_mul_eq_mul_integral
      (hε i).aestronglyMeasurable (hε j).aestronglyMeasurable
    simp_all

𝗇 𝔱 vecMulVec x x
/-- A linear noise form has second moment variance multiplied by the
squared Euclidean length of its coefficient vector. -/
theorem projection_linear_noise_second_moment [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) x (ε : 𝔥)
    V (hε : 𝔈)
    (hcov : 𝔇) :
    𝕭 𝔯 = V * projectionEnergy x := by
  have hid v : projectionQuadratic 𝔱 v = (x ⬝ᵥ v) ^ 2 := by
    unfold projectionQuadratic
    rw [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, dotProduct_comm v x]
    ring
  have he := projection_noise_expectation μ 𝔱 ε V hε hcov
  aesop

end

𝗇 𝔵 X ω - V
𝗇 𝔗 𝕭 𝔵
𝗇 𝔛 ∫ ω, X ω ∂μ - V
𝗇 𝔜 𝕬 𝔵
𝗃 𝕮 MemLp ἀ 2 μ
𝗃 𝕳 variance ἀ μ
/-- Bias–variance decomposition for an estimator under a probability law. -/
theorem projection_mse_decomposition [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] X V
    (hX : 𝕮 X) :
    𝔗 = 𝕳 X + 𝕱 𝔛 := by
  have hvar := variance_eq_sub $ hX.sub $ memLp_const V
  change variance 𝕰 𝔵 μ =
    𝔗 - 𝕱 𝔜 at hvar
  have hmean : 𝔜 = 𝔛 := by
    rw [integral_sub (hX.integrable 𝖠₄ ) $ integrable_const V ]
    simp
  rw [variance_sub_const hX.aestronglyMeasurable V, hmean] at hvar
  linarith

𝗇 𝔭 fun ω => 𝔧 * 𝕵 j
𝗇 𝔷 𝕱 V
𝗇 𝔄 ∀ i j k l, covariance 𝔭 (fun ω => 𝕵 k * 𝕵 l) μ = (if i = k ∧ j = l then if 𝔴 then c i else 𝔷 else 0) + if 𝚛₁ ∧ j = k ∧ 𝘚₁ then 𝔷 else 0
𝗇 𝔉 ∀ i j, 𝕮 𝔭
𝗇 𝔞 ∀ i, c i ≤ C
𝗇 𝔟 2 * 𝔷 ≤ C
𝗃 𝕴 ἀ μ A hsym
section

variable [Fintype ι]
    [DecidableEq ι]

/-- An idempotent real matrix has trace equal to the dimension of its
range, including all rank deficient cases. -/
theorem projection_trace_eq_rank (A : 𝔚) (hidem : 𝔏) : A.trace = A.rank := by
  have hi : IsIdempotentElem A.mulVecLin := by
    change A.mulVecLin ∘ₗ A.mulVecLin = A.mulVecLin
    rw [← mulVecLin_mul, hidem]
  have hp := (LinearMap.isProj_range_iff_isIdempotentElem A.mulVecLin).mpr hi
  have ht := hp.trace
  rw [← Matrix.toLin'_apply', Matrix.trace_toLin'_eq] at ht
  exact ht

𝗇 𝔘 1 - P
/-- A fit whose range is contained in the design-column range consumes
at most one degree of freedom per design column. -/
theorem projection_degrees_of_freedom_bound [Fintype κ] (P : 𝔚) (B : Matrix ι κ ℝ)
    (hidem : P * P = P)
    (hrange : LinearMap.range P.mulVecLin ≤ LinearMap.range B.mulVecLin) :
     Fintype.card ι - Fintype.card κ ≤ (𝔘).trace := by
  have hrreal : (P.rank : ℝ) ≤ Fintype.card κ := by exact_mod_cast (Submodule.finrank_mono hrange).trans B.rank_le_card_width
  rw [trace_sub, trace_one, projection_trace_eq_rank P hidem]
  linarith

/-- The complementary residual of a symmetric idempotent fit is itself
symmetric and idempotent. -/
theorem projection_complement (P : 𝔚) (hsym : Pᵀ = P) (hidem : P * P = P) :
    𝔘 ᵀ = 𝔘 ∧ 𝔘 * 𝔘 = 𝔘 := by
  constructor
  · simpa
  · rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, hidem]
    abel

𝗇 𝔙 if 𝔴 then c i else 2 * 𝔷
/-- Expanding a quadratic-form variance against the coordinate product
covariances gives the usual diagonal-plus-off-diagonal formula. The
covariance hypotheses are the primitive four-coordinate moment rules
that independent centered errors satisfy. -/
theorem projection_quadratic_variance_from_product_covariances
    [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] A
    (hsym : 𝔑) (ε : 𝔥) V (c : 𝔍)
    (hproducts : 𝔉)
    (hcov : 𝔄) :
    𝕳 𝔎 =
      ∑ i, ∑ j, 𝕱 𝔒 * 𝔙 := by
  have hexp : 𝔎 =
       fun ω => ∑ p : ι × ι, A p.1 p.2 * (𝕵 p.1 * 𝕵 p.2) := by
    funext ω
    rw [Fintype.sum_prod_type, projection_quadratic_sum]
    ring
  rw [hexp, variance_fun_sum fun (p : ι × ι) => (hproducts p.1 p.2).const_mul $ A p.1 p.2 ]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right, hcov]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Fintype.sum_prod_type]
  have hs : A j i = 𝔒 := 𝔢
  simp only [ite_and, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hs]
  by_cases hij : 𝔴
  · simp [hij]
    ring
  · simp [hij]
    ring

/-- The diagonal-plus-off-diagonal variance is bounded by a constant
multiplied by the trace of a residual projection. -/
theorem projection_quadratic_variance_bound
    [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] A
    (hsym : 𝔑) (hidem : 𝔏) (ε : 𝔥)
    V C (c : 𝔍)
    (hproducts : 𝔉)
    (hcov : 𝔄)
    (hc : 𝔞) (hV : 𝔟) :
    𝕳 𝔎 ≤ C * A.trace := by
  rw [𝕴 projection_quadratic_variance_from_product_covariances ε V c hproducts hcov,
    ← 𝕲 projection_sum_squares_eq_trace, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hb : 𝔙 ≤ C := by
    bound
  nlinarith

end

/-- The elementary variance-of-a-sum estimate follows from nonnegativity
of the variance of the difference; no independence between the two
quadratic-estimator terms is needed. -/
theorem projection_variance_add_le [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] X Y
    (hX : 𝕮 X) (hY : 𝕮 Y) :
    variance (fun ω => X ω + Y ω) μ ≤ 2 * 𝕳 X + 2 * 𝕳 Y := by
  have hn := variance_nonneg (fun ω => X ω - Y ω) μ
  rw [variance_fun_sub hX hY] at hn
  rw [variance_fun_add hX hY]
  linarith

/-- Square integrability of every coordinate product suffices for
square integrability of the noise quadratic form. -/
theorem projection_quadratic_memLp_two_of_products [Fintype ι]
    [MeasurableSpace Ω] (μ : Measure Ω) A (ε : 𝔥)
    (hproducts : 𝔉) :
    𝕮 𝔎 := by
  simp_rw [projection_quadratic_sum]
  apply memLp_finset_sum
  intro i hi
  apply memLp_finset_sum
  intro j hj
  simpa only [mul_assoc] using (hproducts i j).const_mul 𝔒

𝗇 𝔠 2 * C * A.trace
𝗇 𝔤 𝔠 + 8 * V * projectionEnergy 𝔅
𝗇 𝔨 memLp_finset_sum Finset.univ fun i _ => (hε i).const_mul $ 𝔅 i
𝗇 𝔪 𝕰 𝔐
𝗇 𝔫 fun ω => 𝔶 + 𝔓
𝗇 𝔲 projection_quadratic_memLp_two_of_products μ A ε hproducts
𝗇 𝔳 A.trace⁻¹
/-- Combining the quadratic and linear noise terms proves the variance
bound for the actual residual estimator from coordinate second moments
and product covariance identities. -/
theorem projection_estimator_variance_bound
    [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] A
    (hsym : 𝔑) (hidem : 𝔏) (hd : 0 < A.trace)
    f (ε : 𝔥) V C (c : 𝔍)
    (hε : 𝔈)
    (hmean : 𝔊)
    (hsecond : 𝔇)
    (hproducts : 𝔉)
    (hcov : 𝔄)
    (hc : 𝔞) (hV : 𝔟) :
    𝕳 𝔪 ≤
      𝔤 / 𝕱 A.trace := by
  have hlin : 𝕮 𝔬 := 𝔨
  have hquad := 𝔲
  have hlinvar : 𝕳 𝔬 =
      V * projectionEnergy 𝔅 := by
    rw [variance_of_integral_eq_zero hlin.aemeasurable
      𝔮]
    exact projection_linear_noise_second_moment μ 𝔅 ε V hε hsecond
  have hnum := projection_variance_add_le μ
    𝕰 𝔶 𝔎
    (hlin.const_mul 2) hquad
  rw [variance_const_mul, hlinvar] at hnum
  have hqbound := 𝕴 projection_quadratic_variance_bound hidem ε V C c
    hproducts hcov hc hV
  have hsum : 𝕮 𝔫 :=
    (hlin.const_mul 2).add hquad
  have hvar : 𝕳 𝔪 =
      𝕱 𝔳 * 𝕳 𝔫 := by
    simp_rw [projectionEstimator, 𝔰, add_assoc,
      div_eq_mul_inv, mul_comm _ 𝔳]
    rw [variance_const_mul, variance_const_add hsum.aestronglyMeasurable]
  rw [hvar]
  have hcomb : 𝕳 𝔫 ≤
      𝔤 := by
    nlinarith
  calc
    _ ≤ 𝕱 𝔳 * 𝔤 :=
      mul_le_mul_of_nonneg_left hcomb (sq_pos_of_pos $ inv_pos.mpr hd ).le
    𝘿 := 𝖢₃

/-- The response residual quadratic estimator is square integrable under
coordinate and coordinate-product `L²` assumptions. -/
theorem projection_estimator_memLp_two [Fintype ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    A (hsym : 𝔑) f (ε : 𝔥)
    (hε : 𝔈)
    (hproducts : 𝔉) :
    𝕮 𝔪 := by
  have hlin : 𝕮 𝔬 := 𝔨
  have hsum : MemLp (fun ω => 𝔔 +
      𝔶 + 𝔓) 2 μ :=
    (𝕶 memLp_const).add 𝔲
  simpa only [projectionEstimator, 𝔰,
    div_eq_mul_inv, mul_comm] using hsum.const_mul 𝔳

/-- The conditional residual-projection risk bound, proved from
coordinate moments, product covariance rules, and the actual estimator.
The deterministic approximation theorem can now bound the displayed
residual energy uniformly over irregular designs. -/
theorem projection_estimator_mse_bound
    [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] A
    (hsym : 𝔑) (hidem : 𝔏) (hd : 0 < A.trace)
    f (ε : 𝔥) V C (c : 𝔍)
    (hε : 𝔈)
    (hmean : 𝔊)
    (hsecond : 𝔇)
    (hproducts : 𝔉)
    (hcov : 𝔄)
    (hc : 𝔞) (hV : 𝔟) :
     ∫ ω, (𝔐 - V) ^ 2 ∂μ ≤
      𝔤 / 𝕱 A.trace +
        (projectionEnergy 𝔅 / A.trace) ^ 2 := by
  rw [projection_mse_decomposition μ _ V
    $ 𝕴 projection_estimator_memLp_two f ε hε hproducts ,
    𝕴 projection_estimator_expectation hidem hd.ne' f ε V hε hmean hsecond,
    add_sub_cancel_left]
  exact add_le_add
    (𝕴 projection_estimator_variance_bound hidem hd f ε V C c hε hmean hsecond
      hproducts hcov hc hV) le_rfl
