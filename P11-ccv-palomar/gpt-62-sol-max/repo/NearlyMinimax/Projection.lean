module

public import Mathlib

@[expose] public section

/-!
# Residual projection algebra

The deterministic matrix identities and expectation calculation behind
Lemma `projection-upper`.  These statements permit rank deficient design
matrices: only the symmetric idempotent residual matrix is required.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace NearlyMinimax

set_option backward.isDefEq.respectTransparency false

/-- Squared Euclidean length, independent of the sup norm on function spaces. -/
def projectionEnergy {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := x ⬝ᵥ x

/-- The residual quadratic numerator. -/
def projectionQuadratic {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x)

/-- The residual variance estimator before clipping. -/
def projectionEstimator {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  projectionQuadratic A x / A.trace

section
variable {ι : Type*} [Fintype ι]

theorem projectionEnergy_nonneg (x : ι → ℝ) :
    0 ≤ projectionEnergy x := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

section
variable (A : Matrix ι ι ℝ) (hsym : Aᵀ = A) (hidem : A * A = A)
include hsym hidem

/-- The Frobenius square of a symmetric projection equals its trace. -/
theorem projection_sum_squares_eq_trace :
    (∑ i, ∑ j, A i j ^ 2) = A.trace := by
  calc
    (∑ i, ∑ j, A i j ^ 2) = (A * A).trace := by
      unfold trace diag
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_apply]
      apply Finset.sum_congr rfl
      intro j hj
      have hs : A j i = A i j := congrArg (fun M : Matrix ι ι ℝ => M i j) hsym
      rw [hs, pow_two]
    _ = A.trace := by simp_all

section
variable (f : ι → ℝ)

/-- For a symmetric idempotent matrix, the quadratic form is precisely
the residual's squared Euclidean length. -/
theorem projection_quadratic_eq_energy :
    projectionQuadratic A f = projectionEnergy (A *ᵥ f) := by
  unfold projectionQuadratic projectionEnergy
  symm
  rw [dotProduct_mulVec, ← mulVec_transpose, hsym, mulVec_mulVec, hidem, dotProduct_comm]

/-- The residual and fitted components are orthogonal. -/
theorem projection_orthogonal :
    (A *ᵥ f) ⬝ᵥ (f - A *ᵥ f) = 0 := by
  rw [dotProduct_sub]
  have h := projection_quadratic_eq_energy A hsym hidem f
  unfold projectionQuadratic projectionEnergy at h
  rw [dotProduct_comm (A *ᵥ f) f, h, sub_self]

/-- A symmetric projection cannot increase Euclidean length. -/
theorem projection_energy_le :
    projectionEnergy (A *ᵥ f) ≤ projectionEnergy f := by
  have horth := projection_orthogonal A hsym hidem f
  have hpos := projectionEnergy_nonneg (f - A *ᵥ f)
  have hdecomp : projectionEnergy f = projectionEnergy (A *ᵥ f) +
      projectionEnergy (f - A *ᵥ f) := by
    have hid : f = A *ᵥ f + (f - A *ᵥ f) := by abel
    conv_lhs => rw [hid]
    unfold projectionEnergy
    rw [dotProduct_add, add_dotProduct, add_dotProduct, horth,
      dotProduct_comm (f - A *ᵥ f) (A *ᵥ f), horth]
    ring
  linarith

end

/-- Any candidate fitted vector killed by the residual projection gives
an upper bound for the residual approximation error. -/
theorem projection_residual_minimality
    (f q : ι → ℝ) (hq : A *ᵥ q = 0) :
    projectionEnergy (A *ᵥ f) ≤ projectionEnergy (f - q) := by
  have hAq : A *ᵥ (f - q) = A *ᵥ f := by rw [mulVec_sub, hq, sub_zero]
  rw [← hAq]
  apply projection_energy_le <;> assumption

end

theorem projectionEnergy_le_of_abs_le (f : ι → ℝ) (b : ℝ) (h : ∀ i, |f i| ≤ b) :
    projectionEnergy f ≤ Fintype.card ι * b ^ 2 := by
  unfold projectionEnergy dotProduct
  calc
    _ ≤ ∑ _i : ι, b ^ 2 := Finset.sum_le_sum (fun i _ => by
      simpa only [pow_two] using sq_le_sq.mpr ((h i).trans (le_abs_self b)))
    _ = _ := by simp [nsmul_eq_mul]

section
variable (A : Matrix ι ι ℝ)

section
variable (hsym : Aᵀ = A)
include hsym

/-- A pointwise polynomial approximation of size `b` bounds the total
residual squared error by the sample size multiplied by `b²`. -/
theorem projection_approximation_bound (hidem : A * A = A)
    (f q : ι → ℝ) (hq : A *ᵥ q = 0) (b : ℝ)
    (happrox : ∀ i, |f i - q i| ≤ b) :
    projectionEnergy (A *ᵥ f) ≤ Fintype.card ι * b ^ 2 := by
  exact (projection_residual_minimality A hsym hidem f q hq).trans
    (projectionEnergy_le_of_abs_le (f - q) b happrox)

/-- Quadratic expansion separates approximation bias, the linear noise
term, and the centered noise quadratic form. -/
theorem projection_quadratic_add (f ε : ι → ℝ) :
    projectionQuadratic A (f + ε) = projectionQuadratic A f +
      2 * ((A *ᵥ f) ⬝ᵥ ε) + projectionQuadratic A ε := by
  unfold projectionQuadratic
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct]
  have hcross : f ⬝ᵥ (A *ᵥ ε) = (A *ᵥ f) ⬝ᵥ ε := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym]
  rw [hcross, dotProduct_comm ε (A *ᵥ f)]
  ring

end

/-- Entrywise expansion of the actual quadratic form. -/
theorem projection_quadratic_sum (x : ι → ℝ) :
    projectionQuadratic A x = ∑ i, ∑ j, A i j * (x i * x j) := by
  unfold projectionQuadratic mulVec dotProduct
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl <;> grind

end

end

section
variable {ι Ω : Type*} [Fintype ι]

section
variable [MeasurableSpace Ω]

section
variable {μ : Measure Ω}

private theorem linear_noise_memLp_two
    (x : ι → ℝ) {ε : Ω → ι → ℝ} (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ) :
    MemLp (fun ω => x ⬝ᵥ ε ω) 2 μ :=
  memLp_finset_sum _ (fun i _ => (hε i).const_mul (x i))

private theorem scaled_noise_product_integrable
    {ε : Ω → ι → ℝ} (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ) (c : ℝ) (i j : ι) :
    Integrable (fun ω => c * (ε ω i * ε ω j)) μ :=
  ((hε i).integrable_mul (hε j)).const_mul c

end

/-- Finite quadratic noise forms are integrable under coordinate `L²` bounds. -/
theorem projection_quadratic_integrable (μ : Measure Ω) (A : Matrix ι ι ℝ) (ε : Ω → ι → ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ) :
    Integrable (fun ω => projectionQuadratic A (ε ω)) μ := by
  simp_rw [projection_quadratic_sum]
  exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _
    (fun j _ => scaled_noise_product_integrable hε (A i j) i j))

end

/-- The expected noise quadratic form is variance times trace.  The
hypothesis gives ordinary coordinate second moments, not a conclusion
about the quadratic form. -/
theorem projection_noise_expectation [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) (A : Matrix ι ι ℝ) (ε : Ω → ι → ℝ)
    (V : ℝ) (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hcov : ∀ i j, (∫ ω, ε ω i * ε ω j ∂μ) = if i = j then V else 0) :
    (∫ ω, projectionQuadratic A (ε ω) ∂μ) = V * A.trace := by
  have hij i j := scaled_noise_product_integrable hε (A i j) i j
  simp_rw [projection_quadratic_sum]
  rw [integral_finset_sum Finset.univ (fun i _ => integrable_finset_sum _ (fun j _ => hij i j))]
  simp_rw [integral_finset_sum Finset.univ (fun j _ => hij _ j),
    integral_const_mul, hcov, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  unfold trace diag
  rw [Finset.mul_sum] <;> grind

/-- Centered coordinate noise has zero expectation in every linear form. -/
theorem projection_linear_noise_expectation
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : ι → ℝ) (ε : Ω → ι → ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hmean : ∀ i, (∫ ω, ε ω i ∂μ) = 0) :
    (∫ ω, x ⬝ᵥ ε ω ∂μ) = 0 := by
  unfold dotProduct
  rw [integral_finset_sum Finset.univ (fun i _ =>
    ((hε i).integrable (by norm_num)).const_mul (x i))]
  simp [integral_const_mul, hmean, mul_zero]

section
variable [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω)

/-- The residual estimator's conditional expectation is variance plus
squared approximation residual divided by the degrees of freedom. -/
theorem projection_estimator_expectation [IsProbabilityMeasure μ]
    (A : Matrix ι ι ℝ) (hsym : Aᵀ = A) (hidem : A * A = A)
    (hd : A.trace ≠ 0) (f : ι → ℝ) (ε : Ω → ι → ℝ) (V : ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hmean : ∀ i, (∫ ω, ε ω i ∂μ) = 0)
    (hcov : ∀ i j, (∫ ω, ε ω i * ε ω j ∂μ) = if i = j then V else 0) :
    (∫ ω, projectionEstimator A (f + ε ω) ∂μ) =
      V + projectionEnergy (A *ᵥ f) / A.trace := by
  have hlin : Integrable (fun ω => (A *ᵥ f) ⬝ᵥ ε ω) μ :=
    (linear_noise_memLp_two (A *ᵥ f) hε).integrable (by norm_num)
  have hquad := projection_quadratic_integrable μ A ε hε
  have hsum : Integrable (fun ω => projectionQuadratic A f + 2 * ((A *ᵥ f) ⬝ᵥ ε ω)) μ :=
    (integrable_const (projectionQuadratic A f)).add (hlin.const_mul 2)
  simp_rw [projectionEstimator, projection_quadratic_add A hsym f]
  rw [integral_div, integral_add hsum hquad,
    integral_add (integrable_const (projectionQuadratic A f)) (hlin.const_mul 2), integral_const,
    probReal_univ, one_smul, integral_const_mul,
    projection_linear_noise_expectation μ (A *ᵥ f) ε hε hmean,
    mul_zero, add_zero, projection_noise_expectation μ A ε V hε hcov,
    projection_quadratic_eq_energy A hsym hidem f]
  field_simp
  ring

/-- Independence and centered errors imply the coordinate covariance
identities used by the quadratic expectation theorem. -/
theorem projection_coordinate_covariance [IsProbabilityMeasure μ]
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
    simp_all

/-- A linear noise form has second moment variance multiplied by the
squared Euclidean length of its coefficient vector. -/
theorem projection_linear_noise_second_moment (x : ι → ℝ) (ε : Ω → ι → ℝ)
    (V : ℝ) (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hcov : ∀ i j, (∫ ω, ε ω i * ε ω j ∂μ) = if i = j then V else 0) :
    (∫ ω, (x ⬝ᵥ ε ω) ^ 2 ∂μ) = V * projectionEnergy x := by
  have hid (v : ι → ℝ) : projectionQuadratic (vecMulVec x x) v = (x ⬝ᵥ v) ^ 2 := by
    unfold projectionQuadratic
    simp [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, dotProduct_comm v x] <;> ring
  have he := projection_noise_expectation μ (vecMulVec x x) ε V hε hcov
  simp_rw [hid] at he
  assumption

end

end

/-- Bias–variance decomposition for an estimator under a probability law. -/
theorem projection_mse_decomposition {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (V : ℝ)
    (hX : MemLp X 2 μ) :
    (∫ ω, (X ω - V) ^ 2 ∂μ) = variance X μ + ((∫ ω, X ω ∂μ) - V) ^ 2 := by
  have h := variance_eq_sub (hX.sub (memLp_const V))
  change variance (fun ω => X ω - V) μ = (∫ ω, (X ω - V) ^ 2 ∂μ) - (∫ ω, X ω - V ∂μ) ^ 2 at h
  rw [variance_sub_const hX.aestronglyMeasurable, integral_sub (hX.integrable (by norm_num)) (integrable_const V)] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  linarith

/-- An idempotent real matrix has trace equal to the dimension of its
range, including all rank deficient cases. -/
theorem projection_trace_eq_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hidem : A * A = A) : A.trace = A.rank := by
  have hi : IsIdempotentElem A.mulVecLin := by
    change A.mulVecLin ∘ₗ A.mulVecLin = A.mulVecLin
    rw [← mulVecLin_mul, hidem]
  have hp := (LinearMap.isProj_range_iff_isIdempotentElem A.mulVecLin).mpr hi
  have ht := hp.trace
  change LinearMap.trace ℝ (ι → ℝ) A.mulVecLin = (A.rank : ℝ) at ht
  simpa [← Matrix.toLin'_apply', Matrix.trace_toLin'_eq] using ht

/-- A fit whose range is contained in the design-column range consumes
at most one degree of freedom per design column. -/
theorem projection_degrees_of_freedom_bound {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] (P : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (hidem : P * P = P)
    (hrange : LinearMap.range P.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    (Fintype.card ι : ℝ) - Fintype.card κ ≤ (1 - P).trace := by
  have hr :=
    (Submodule.finrank_mono hrange).trans B.rank_le_card_width
  have hrreal : (P.rank : ℝ) ≤ Fintype.card κ := by exact_mod_cast hr
  rw [trace_sub, trace_one, projection_trace_eq_rank P hidem]
  linarith

/-- The complementary residual of a symmetric idempotent fit is itself
symmetric and idempotent. -/
theorem projection_complement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hsym : Pᵀ = P) (hidem : P * P = P) :
    (1 - P)ᵀ = 1 - P ∧ (1 - P) * (1 - P) = 1 - P := by
  constructor
  · rw [transpose_sub, transpose_one, hsym]
  · rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, hidem]
    abel

/-- Quadratic monomials covary only on a matched index pair. The reversed
pair contributes separately off the diagonal. -/
def HasProjectionProductCovariance {ι Ω : Type*} [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (ε : Ω → ι → ℝ) (V : ℝ) (c : ι → ℝ) : Prop :=
  ∀ p q : ι × ι,
    covariance (fun ω => ε ω p.1 * ε ω p.2) (fun ω => ε ω q.1 * ε ω q.2) μ =
      (if q = p then (if p.1 = p.2 then c p.1 else V ^ 2) else 0) +
      (if q = p.swap ∧ p.1 ≠ p.2 then V ^ 2 else 0)

section
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Matrix ι ι ℝ)
    (hsym : Aᵀ = A)
include hsym

/-- Expanding a quadratic-form variance against the coordinate product
covariances gives the usual diagonal-plus-off-diagonal formula.  The
covariance hypotheses are the primitive four-coordinate moment rules
that independent centered errors satisfy. -/
theorem projection_quadratic_variance_from_product_covariances (ε : Ω → ι → ℝ) (V : ℝ) (c : ι → ℝ)
    (hproducts : ∀ i j, MemLp (fun ω => ε ω i * ε ω j) 2 μ)
    (hcov : HasProjectionProductCovariance μ ε V c) :
    variance (fun ω => projectionQuadratic A (ε ω)) μ =
      ∑ i, ∑ j, A i j ^ 2 * (if i = j then c i else 2 * V ^ 2) := by
  rw [show (fun ω => projectionQuadratic A (ε ω)) =
    (fun ω => ∑ p : ι × ι, A p.1 p.2 * (ε ω p.1 * ε ω p.2)) by
      funext ω; rw [Fintype.sum_prod_type, projection_quadratic_sum], variance_fun_sum (fun (p : ι × ι) => (hproducts p.1 p.2).const_mul (A p.1 p.2))]
  unfold HasProjectionProductCovariance at hcov
  simp_rw [covariance_const_mul_left, covariance_const_mul_right]
  simp_rw [hcov]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl fun j _ => ?_)
  have hs : A j i = A i j := congrArg (fun M : Matrix ι ι ℝ => M i j) hsym
  by_cases hij : i = j <;>
    simp [hij, mul_add, mul_ite, Finset.sum_add_distrib, Finset.sum_ite_eq', hs] <;> ring

/-- The diagonal-plus-off-diagonal variance is bounded by a constant
multiplied by the trace of a residual projection. -/
theorem projection_quadratic_variance_bound (hidem : A * A = A) (ε : Ω → ι → ℝ)
    (V C : ℝ) (c : ι → ℝ)
    (hproducts : ∀ i j, MemLp (fun ω => ε ω i * ε ω j) 2 μ)
    (hcov : HasProjectionProductCovariance μ ε V c)
    (hc : ∀ i, c i ≤ C) (hV : 2 * V ^ 2 ≤ C) :
    variance (fun ω => projectionQuadratic A (ε ω)) μ ≤ C * A.trace := by
  rw [projection_quadratic_variance_from_product_covariances μ A hsym ε V c hproducts hcov,
    ← projection_sum_squares_eq_trace A hsym hidem]
  simp_rw [Finset.mul_sum, mul_comm C]
  gcongr with i _ j _
  split_ifs <;> first | apply hc | exact hV

end

/-- The elementary variance-of-a-sum estimate follows from nonnegativity
of the variance of the difference; no independence between the two
quadratic-estimator terms is needed. -/
theorem projection_variance_add_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    variance (fun ω => X ω + Y ω) μ ≤ 2 * variance X μ + 2 * variance Y μ := by
  have hn := variance_nonneg (fun ω => X ω - Y ω) μ
  rw [variance_fun_sub hX hY] at hn
  rw [variance_fun_add hX hY]
  linarith

section
variable {ι Ω : Type*} [Fintype ι]

/-- Square integrability of every coordinate product suffices for
square integrability of the noise quadratic form. -/
theorem projection_quadratic_memLp_two_of_products
    [MeasurableSpace Ω] (μ : Measure Ω) (A : Matrix ι ι ℝ) (ε : Ω → ι → ℝ)
    (hproducts : ∀ i j, MemLp (fun ω => ε ω i * ε ω j) 2 μ) :
    MemLp (fun ω => projectionQuadratic A (ε ω)) 2 μ := by
  simp_rw [projection_quadratic_sum]
  apply memLp_finset_sum
  intro i hi
  apply memLp_finset_sum
  intro j hj
  exact (hproducts i j).const_mul (A i j)

/-- Combining the quadratic and linear noise terms proves the variance
bound for the actual residual estimator from coordinate second moments
and product covariance identities. -/
theorem projection_estimator_variance_bound [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Matrix ι ι ℝ)
    (hsym : Aᵀ = A) (hidem : A * A = A)
    (f : ι → ℝ) (ε : Ω → ι → ℝ) (V C : ℝ) (c : ι → ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hmean : ∀ i, (∫ ω, ε ω i ∂μ) = 0)
    (hsecond : ∀ i j, (∫ ω, ε ω i * ε ω j ∂μ) = if i = j then V else 0)
    (hproducts : ∀ i j, MemLp (fun ω => ε ω i * ε ω j) 2 μ)
    (hcov : HasProjectionProductCovariance μ ε V c)
    (hc : ∀ i, c i ≤ C) (hV : 2 * V ^ 2 ≤ C) :
    variance (fun ω => projectionEstimator A (f + ε ω)) μ ≤
      (2 * C * A.trace + 8 * V * projectionEnergy (A *ᵥ f)) / A.trace ^ 2 := by
  have hlin := linear_noise_memLp_two (A *ᵥ f) hε
  have hquad := projection_quadratic_memLp_two_of_products μ A ε hproducts
  have hnum := projection_variance_add_le μ _ _ (hlin.const_mul 2) hquad
  rw [variance_const_mul, variance_of_integral_eq_zero hlin.aemeasurable
    (projection_linear_noise_expectation μ _ ε hε hmean),
    projection_linear_noise_second_moment μ _ ε V hε hsecond] at hnum
  have hmeas : AEStronglyMeasurable (fun ω => 2 * ((A *ᵥ f) ⬝ᵥ ε ω) + projectionQuadratic A (ε ω)) μ :=
    ((hlin.const_mul 2).add hquad).aestronglyMeasurable
  simp [projectionEstimator, projection_quadratic_add A hsym f, add_assoc,
    div_eq_mul_inv, mul_comm _ A.trace⁻¹, variance_const_mul, variance_const_add hmeas, ← inv_pow]
  rw [mul_comm _ (A.trace⁻¹ ^ 2)]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  linarith only [hnum, projection_quadratic_variance_bound μ A hsym hidem ε V C c hproducts hcov hc hV]

/-- The response residual quadratic estimator is square integrable under
coordinate and coordinate-product `L²` assumptions. -/
theorem projection_estimator_memLp_two
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix ι ι ℝ) (hsym : Aᵀ = A) (f : ι → ℝ) (ε : Ω → ι → ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hproducts : ∀ i j, MemLp (fun ω => ε ω i * ε ω j) 2 μ) :
    MemLp (fun ω => projectionEstimator A (f + ε ω)) 2 μ := by
  have hlin := linear_noise_memLp_two (A *ᵥ f) hε
  have hquad := projection_quadratic_memLp_two_of_products μ A ε hproducts
  have hsum : MemLp (fun ω => projectionQuadratic A f +
      2 * ((A *ᵥ f) ⬝ᵥ ε ω) + projectionQuadratic A (ε ω)) 2 μ :=
    ((memLp_const (projectionQuadratic A f)).add (hlin.const_mul 2)).add hquad
  simpa only [projectionEstimator, projection_quadratic_add A hsym f,
    div_eq_mul_inv, mul_comm] using hsum.const_mul A.trace⁻¹

/-- The conditional residual-projection risk bound, proved from
coordinate moments, product covariance rules, and the actual estimator.
The deterministic approximation theorem can now bound the displayed
residual energy uniformly over irregular designs. -/
theorem projection_estimator_mse_bound [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Matrix ι ι ℝ)
    (hsym : Aᵀ = A) (hidem : A * A = A) (hd : 0 < A.trace)
    (f : ι → ℝ) (ε : Ω → ι → ℝ) (V C : ℝ) (c : ι → ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hmean : ∀ i, (∫ ω, ε ω i ∂μ) = 0)
    (hsecond : ∀ i j, (∫ ω, ε ω i * ε ω j ∂μ) = if i = j then V else 0)
    (hproducts : ∀ i j, MemLp (fun ω => ε ω i * ε ω j) 2 μ)
    (hcov : HasProjectionProductCovariance μ ε V c)
    (hc : ∀ i, c i ≤ C) (hV : 2 * V ^ 2 ≤ C) :
    (∫ ω, (projectionEstimator A (f + ε ω) - V) ^ 2 ∂μ) ≤
      (2 * C * A.trace + 8 * V * projectionEnergy (A *ᵥ f)) / A.trace ^ 2 +
        (projectionEnergy (A *ᵥ f) / A.trace) ^ 2 := by
  rw [projection_mse_decomposition μ _ V
    (projection_estimator_memLp_two μ A hsym f ε hε hproducts),
    projection_estimator_expectation μ A hsym hidem hd.ne' f ε V hε hmean hsecond,
    add_sub_cancel_left]
  exact add_le_add
    (projection_estimator_variance_bound μ A hsym hidem f ε V C c hε hmean hsecond
      hproducts hcov hc hV) le_rfl

end

end NearlyMinimax
