module

public import NearlyMinimax.LowSmoothnessGridExperiment
public import NearlyMinimax.PathRisk

@[expose] public section

/-! Actual augmented design--activation--response probability measures.
The conditional finite weights and scores are those of the low-smoothness
experiment. Markov normalization and all integral identities are proved. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev LowMixtureMarks (m n : ℕ) := (TernaryVector m) × (TernaryVector n)

def lowMixtureWeight {α : Type*} {m n : ℕ} (a V t : ℝ)
    (f : α → (TernaryVector m) → Fin n → ℝ) (x : α)
    (z : LowMixtureMarks m n) : ℝ :=
  activationProductPrior t z.1 * finiteResponseLikelihood a V (f x) z.1 z.2

section
variable {α : Type*} [MeasurableSpace α] {m n : ℕ} (a V t : ℝ) {f : α → (TernaryVector m) → Fin n → ℝ}
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i))

include hf in
theorem lowMixtureWeight_measurable (z : LowMixtureMarks m n) :
    Measurable (fun x => lowMixtureWeight a V t f x z) := (Finset.measurable_prod _ (fun i _ =>
    ternaryMass_measurable_comp a V _ (hf z.1 i) (z.2 i))).const_mul _

def lowMixtureIndexKernel : Kernel α (LowMixtureMarks m n) where
  toFun x := ∑ z,
    ENNReal.ofReal (lowMixtureWeight a V t f x z) • Measure.dirac z
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ (fun z _ =>
      (ENNReal.measurable_ofReal.comp (lowMixtureWeight_measurable a V t hf z)).mul_const _)

theorem lowMixtureIndexKernel_apply
    (m n : ℕ) (a V t : ℝ) (f : α → (TernaryVector m) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (x : α) :
    lowMixtureIndexKernel a V t hf x =
      ∑ z,
        ENNReal.ofReal (lowMixtureWeight a V t f x z) • Measure.dirac z := rfl

end

theorem lowMixtureWeight_nonneg {α : Type*} {m n : ℕ} {a V t : ℝ}
    {f : α → (TernaryVector m) → Fin n → ℝ} (ht : t ∈ Icc 0 1)
    (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y) (x : α) (z : LowMixtureMarks m n) :
    0 ≤ lowMixtureWeight a V t f x z :=
  finite_experiment_joint_nonnegative ht.1 ht.2 (hp x) ..

section
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) {m n : ℕ} (a V t : ℝ)
    {f : α → (TernaryVector m) → Fin n → ℝ} (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)

include ha ht hp in
theorem lowMixtureIndexKernel_markov :
    IsMarkovKernel (lowMixtureIndexKernel a V t hf) := by
  constructor
  intro x
  constructor
  simp [lowMixtureIndexKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ =>
    lowMixtureWeight_nonneg ht hp x z)]
  simp only [lowMixtureWeight, Fintype.sum_prod_type]
  rw [(by simp_rw [← Finset.mul_sum, finite_response_normalized m n a V (f x) _ ha, mul_one]; exact activation_product_prior_normalized m t : ∑ ξ, ∑ y, activationProductPrior t ξ * finiteResponseLikelihood a V (f x) ξ y = 1)]
  simp

include ht hp in
theorem lowMixtureIndexKernel_integral
    (x : α) (H : LowMixtureMarks m n → ℝ) :
    (∫ z, H z ∂lowMixtureIndexKernel a V t hf x) =
      ∑ ξ, activationProductPrior t ξ *
        ∑ y, finiteResponseLikelihood a V (f x) ξ y * H (ξ, y) := by
  rw [lowMixtureIndexKernel_apply, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
      lowMixtureWeight, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro ξ hξ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    have hpos : 0 ≤ activationProductPrior t ξ * finiteResponseLikelihood a V (f x) ξ y :=
      lowMixtureWeight_nonneg ht hp x (ξ, y)
    rw [ENNReal.toReal_ofReal hpos]
    ring
  · intro z hz
    apply MeasureTheory.Integrable.smul_measure_nnreal <;> fun_prop

def lowMixtureLaw : Measure (α × LowMixtureMarks m n) :=
  μ.compProd (lowMixtureIndexKernel a V t hf)

theorem lowMixtureLaw_probability [IsProbabilityMeasure μ] (m n : ℕ) (a V t : ℝ)
    (f : α → (TernaryVector m) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc 0 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y) :
    IsProbabilityMeasure (lowMixtureLaw μ a V t hf) := by
  let := lowMixtureIndexKernel_markov a V t hf ha ht hp
  unfold lowMixtureLaw
  infer_instance

theorem lowMixtureLaw_integrable_of_weighted_norm [IsProbabilityMeasure μ] {m n : ℕ} {a V t : ℝ}
    {f : α → (TernaryVector m) → Fin n → ℝ}
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc 0 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    {H : α × LowMixtureMarks m n → ℝ} (hH : Measurable H)
    (hNorm : Integrable (fun x => ∑ ξ, activationProductPrior t ξ *
      ∑ y, finiteResponseLikelihood a V (f x) ξ y * |H (x, ξ, y)|) μ) :
    Integrable H (lowMixtureLaw μ a V t hf) := by
  let := lowMixtureIndexKernel_markov a V t hf ha ht hp
  apply (Measure.integrable_compProd_iff hH.aestronglyMeasurable).mpr
  constructor
  · aesop
  · simp_rw [lowMixtureIndexKernel_integral a V t hf ht hp,
      Real.norm_eq_abs]
    exact hNorm

theorem lowMixtureLaw_integral
    {μ : Measure α} [IsProbabilityMeasure μ] {m n : ℕ} {a V t : ℝ}
    {f : α → (TernaryVector m) → Fin n → ℝ}
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc 0 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    {H : α × LowMixtureMarks m n → ℝ}
    (hH : Integrable H (lowMixtureLaw μ a V t hf)) :
    (∫ z, H z ∂lowMixtureLaw μ a V t hf) =
      ∫ x, ∑ ξ, activationProductPrior t ξ *
        ∑ y, finiteResponseLikelihood a V (f x) ξ y * H (x, ξ, y) ∂μ := by
  let := lowMixtureIndexKernel_markov a V t hf ha ht hp
  rw [lowMixtureLaw, Measure.integral_compProd hH]
  simp_rw [lowMixtureIndexKernel_integral a V t hf ht hp]

end

section
variable {α : Type*} {m n : ℕ} (a V η t : ℝ) (f : α → (TernaryVector m) → Fin n → ℝ)

def lowMixtureScore (z : α × LowMixtureMarks m n) : ℝ :=
  finiteExperimentScore a V η (f z.1) z.2.1 z.2.2

theorem lowMixtureScore_measurable [MeasurableSpace α]
    {m n : ℕ} (a V η : ℝ) {f : α → (TernaryVector m) → Fin n → ℝ}
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) :
    Measurable (lowMixtureScore a V η f) := by
  apply measurable_from_prod_countable_left
  intro z
  exact finiteExperimentScore_measurable_comp m n a measurable_const f hf η z.1 z.2

def lowMixtureConditionalScoreEnergy (x : α) : ℝ :=
  ∑ ξ, activationProductPrior t ξ * ∑ y,
    finiteResponseLikelihood a V (f x) ξ y *
      finiteExperimentScore a V η (f x) ξ y ^ 2

end

section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] {m n : ℕ} {a V η t : ℝ}
    {f : α → (TernaryVector m) → Fin n → ℝ} (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    (hE : Integrable (lowMixtureConditionalScoreEnergy a V η t f) μ)
include hE ha hp ht

theorem lowMixtureScore_sq_integrable :
    Integrable (fun z => lowMixtureScore a V η f z ^ 2)
      (lowMixtureLaw μ a V t hf) := by
  apply lowMixtureLaw_integrable_of_weighted_norm μ hf ha ht hp
    ((lowMixtureScore_measurable a V η hf).pow_const 2)
  simpa

theorem lowMixtureScore_memLp_two :
    MemLp (lowMixtureScore a V η f) 2 (lowMixtureLaw μ a V t hf) :=
  (memLp_two_iff_integrable_sq (lowMixtureScore_measurable a V η hf).aestronglyMeasurable).mpr
    (lowMixtureScore_sq_integrable hf ha ht hp hE)

end

theorem lowMixtureIndexKernel_score_centered {α : Type*} [MeasurableSpace α]
    {m n : ℕ} (a V η t : ℝ) {f : α → (TernaryVector m) → Fin n → ℝ}
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc 0 1) (hp : ∀ x ξ i y, 0 < ternaryMass a (f x ξ i) V y)
    (x : α) :
    (∫ z, lowMixtureScore a V η f (x, z)
      ∂lowMixtureIndexKernel a V t hf x) = 0 := by
  rw [lowMixtureIndexKernel_integral a V t hf ht
    (fun x ξ i y => (hp x ξ i y).le)]
  unfold lowMixtureScore
  have hc ξ := finite_experiment_score_centered a V η _ ξ ha (fun y => Finset.prod_pos (fun i _ => hp x ξ i (y i)))
  simp_all

section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] {m n : ℕ} {a V η t : ℝ}
    {f : α → (TernaryVector m) → Fin n → ℝ} (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    {H : α × LowMixtureMarks m n → ℝ}
include ha ht

theorem lowMixtureScore_centered (hp : ∀ x ξ i y, 0 < ternaryMass a (f x ξ i) V y)
    (hE : Integrable (lowMixtureConditionalScoreEnergy a V η t f) μ) :
    (∫ z, lowMixtureScore a V η f z ∂lowMixtureLaw μ a V t hf) = 0 := by
  let := lowMixtureIndexKernel_markov a V t hf ha ht (fun x ξ i y => (hp x ξ i y).le)
  let := lowMixtureLaw_probability μ m n a V t f hf ha ht (fun x ξ i y => (hp x ξ i y).le)
  have hi := (lowMixtureScore_memLp_two hf ha ht
    (fun x ξ i y => (hp x ξ i y).le) hE).integrable (by norm_num)
  rw [lowMixtureLaw, Measure.integral_compProd hi]
  simp_rw [lowMixtureIndexKernel_score_centered a V η t hf ha ht hp]
  simp

include hp in
/-- Integrate the design first in each latent state, with all integrability
hypotheses stated on genuine finite response expectations. -/
theorem lowMixtureLaw_integral_sum
    (hH : Integrable H (lowMixtureLaw μ a V t hf))
    (hξ : ∀ ξ, Integrable (fun x => ∑ y,
      finiteResponseLikelihood a V (f x) ξ y * H (x, ξ, y)) μ) :
    (∫ z, H z ∂lowMixtureLaw μ a V t hf) =
      ∑ ξ, activationProductPrior t ξ *
        ∫ x, ∑ y, finiteResponseLikelihood a V (f x) ξ y * H (x, ξ, y) ∂μ := by
  rw [lowMixtureLaw_integral hf ha ht hp hH,
    integral_finsetSum _ (fun ξ _ => (hξ ξ).const_mul _)]
  simp_rw [integral_const_mul]

include hp in
theorem lowMixtureLaw_nonneg_integral_sum (hH : Measurable H) (hnonneg : ∀ z, 0 ≤ H z)
    (hξ : ∀ ξ, Integrable (fun x => ∑ y,
      finiteResponseLikelihood a V (f x) ξ y * H (x, ξ, y)) μ) :
    (∫ z, H z ∂lowMixtureLaw μ a V t hf) =
      ∑ ξ, activationProductPrior t ξ *
        ∫ x, ∑ y, finiteResponseLikelihood a V (f x) ξ y * H (x, ξ, y) ∂μ := by
  have hNorm : Integrable (fun x => ∑ ξ, activationProductPrior t ξ * ∑ y,
      finiteResponseLikelihood a V (f x) ξ y * |H (x, ξ, y)|) μ := by
    have heq : (fun x => ∑ ξ, activationProductPrior t ξ * ∑ y,
        finiteResponseLikelihood a V (f x) ξ y * |H (x, ξ, y)|) =
        (fun x => ∑ ξ, activationProductPrior t ξ * ∑ y,
          finiteResponseLikelihood a V (f x) ξ y * H (x, ξ, y)) := by
      funext x
      apply Finset.sum_congr rfl
      intro ξ hξ
      congr 1
      apply Finset.sum_congr rfl
      aesop
    rw [heq]
    fun_prop
  exact lowMixtureLaw_integral_sum hf ha ht hp
    (lowMixtureLaw_integrable_of_weighted_norm μ hf ha ht hp hH hNorm) hξ

end

variable {α : Type*} [MeasurableSpace α]

theorem lowMixtureScore_sq_integral_eq_sum
    (μ : Measure α) [IsProbabilityMeasure μ] {m n : ℕ} (a V η t : ℝ)
    {f : α → (TernaryVector m) → Fin n → ℝ}
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc 0 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    (hξ : ∀ ξ, Integrable (fun x => ∑ y, finiteResponseLikelihood a V (f x) ξ y *
      finiteExperimentScore a V η (f x) ξ y ^ 2) μ) :
    (∫ z, lowMixtureScore a V η f z ^ 2 ∂lowMixtureLaw μ a V t hf) =
      ∑ ξ, activationProductPrior t ξ * ∫ x,
        ∑ y, finiteResponseLikelihood a V (f x) ξ y *
          finiteExperimentScore a V η (f x) ξ y ^ 2 ∂μ := by
  exact lowMixtureLaw_integral_sum hf ha ht hp (lowMixtureScore_sq_integrable hf ha ht hp (integrable_finsetSum _ (fun ξ _ => (hξ ξ).const_mul _))) hξ

end NearlyMinimax
