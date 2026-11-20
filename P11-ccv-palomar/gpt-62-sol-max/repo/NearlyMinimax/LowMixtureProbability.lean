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

abbrev LowMixtureMarks (m n : ℕ) := (Fin m → Fin 3) × (Fin n → Fin 3)

def lowMixtureWeight {α : Type*} (m n : ℕ) (a V t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ) (x : α)
    (z : LowMixtureMarks m n) : ℝ :=
  activationProductPrior m t z.1 * finiteResponseLikelihood m n a V (f x) z.1 z.2

theorem lowMixtureWeight_measurable {α : Type*} [MeasurableSpace α]
    (m n : ℕ) (a V t : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (z : LowMixtureMarks m n) :
    Measurable (fun x => lowMixtureWeight m n a V t f x z) := by
  exact (Finset.measurable_prod _ (fun i _ =>
      ternaryMass_measurable_comp a V _ (hf z.1 i) (z.2 i))).const_mul _

def lowMixtureIndexKernel {α : Type*} [MeasurableSpace α]
    (m n : ℕ) (a V t : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) : Kernel α (LowMixtureMarks m n) :=
  weightedAtomKernel (lowMixtureWeight m n a V t f) (fun _ z => z)
    (lowMixtureWeight_measurable m n a V t f hf) (fun _ => measurable_const)

section
variable {α : Type*}

theorem lowMixtureWeight_nonneg (m n : ℕ) (a V t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y) (x : α) (z : LowMixtureMarks m n) :
    0 ≤ lowMixtureWeight m n a V t f x z :=
  finite_experiment_joint_nonnegative m n a V t (f x) ht.1 ht.2 (hp x) z.1 z.2

theorem lowMixtureIndexKernel_markov [MeasurableSpace α]
    (m n : ℕ) (a V t : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y) :
    IsMarkovKernel (lowMixtureIndexKernel m n a V t f hf) := by
  apply weightedAtomKernel_markov _ _ _ _ (lowMixtureWeight_nonneg m n a V t f ht hp)
  intro x
  simpa only [lowMixtureWeight, Fintype.sum_prod_type] using finite_experiment_joint_normalized m n a V t (f x) ha

def lowResponseMean (m n : ℕ) (a V : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (H : α × LowMixtureMarks m n → ℝ) (ξ : Fin m → Fin 3) (x : α) : ℝ :=
  ∑ y, finiteResponseLikelihood m n a V (f x) ξ y * H (x, ξ, y)

def lowMixtureMean (m n : ℕ) (a V t : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (H : α × LowMixtureMarks m n → ℝ) (x : α) : ℝ :=
  ∑ ξ, activationProductPrior m t ξ * lowResponseMean m n a V f H ξ x

theorem lowMixtureMean_integrable [MeasurableSpace α] (μ : Measure α)
    (m n : ℕ) (a V t : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (H : α × LowMixtureMarks m n → ℝ) (h : ∀ ξ, Integrable (lowResponseMean m n a V f H ξ) μ) :
    Integrable (lowMixtureMean m n a V t f H) μ :=
  integrable_finsetSum _ (fun ξ _ => (h ξ).const_mul _)

theorem lowMixtureIndexKernel_integral [MeasurableSpace α]
    (m n : ℕ) (a V t : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i))
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    (x : α) (H : α × LowMixtureMarks m n → ℝ) :
    (∫ z, H (x,z) ∂lowMixtureIndexKernel m n a V t f hf x) = lowMixtureMean m n a V t f H x := by
  change (∫ z, H (x,z) ∂weightedAtomMeasure (lowMixtureWeight m n a V t f x) id) = _
  rw [weightedAtomMeasure_integral _ _ (lowMixtureWeight_nonneg m n a V t f ht hp x)]
  simp only [Fintype.sum_prod_type, lowMixtureWeight, lowMixtureMean, lowResponseMean,
    id_eq, Finset.mul_sum, mul_assoc]

end

def lowMixtureLaw {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (m n : ℕ) (a V t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) : Measure (α × LowMixtureMarks m n) :=
  μ.compProd (lowMixtureIndexKernel m n a V t f hf)

section
variable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (m n : ℕ) (a V t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
include ha ht hp

theorem lowMixtureLaw_probability :
    IsProbabilityMeasure (lowMixtureLaw μ m n a V t f hf) := by
  let := lowMixtureIndexKernel_markov m n a V t f hf ha ht hp
  unfold lowMixtureLaw
  infer_instance

theorem lowMixtureLaw_nonneg_integrable_integral
    (H : α × LowMixtureMarks m n → ℝ) (hH : Measurable H) (hn : ∀ z, 0 ≤ H z)
    (hI : Integrable (lowMixtureMean m n a V t f H) μ) :
    Integrable H (lowMixtureLaw μ m n a V t f hf) ∧
      (∫ z, H z ∂lowMixtureLaw μ m n a V t f hf) = ∫ x, lowMixtureMean m n a V t f H x ∂μ := by
  let := lowMixtureIndexKernel_markov m n a V t f hf ha ht hp
  exact finiteKernel_integrable_integral μ _ hH hn
    (fun x => lowMixtureIndexKernel_integral m n a V t f hf ht hp x H) hI

theorem lowMixtureLaw_integral
    (H : α × LowMixtureMarks m n → ℝ)
    (hH : Integrable H (lowMixtureLaw μ m n a V t f hf)) :
    (∫ z, H z ∂lowMixtureLaw μ m n a V t f hf) = ∫ x, lowMixtureMean m n a V t f H x ∂μ := by
  let := lowMixtureIndexKernel_markov m n a V t f hf ha ht hp
  simp [lowMixtureLaw, Measure.integral_compProd hH, lowMixtureIndexKernel_integral m n a V t f hf ht hp]

/-- Integrate the design first in each latent state, for nonnegative observables. -/
theorem lowMixtureLaw_nonneg_moments
    (H : α × LowMixtureMarks m n → ℝ) (hH : Measurable H) (hn : ∀ z, 0 ≤ H z)
    (hξ : ∀ ξ, Integrable (lowResponseMean m n a V f H ξ) μ) :
    Integrable H (lowMixtureLaw μ m n a V t f hf) ∧
    (∫ z, H z ∂lowMixtureLaw μ m n a V t f hf) =
      ∑ ξ, activationProductPrior m t ξ * ∫ x, lowResponseMean m n a V f H ξ x ∂μ := by
  obtain ⟨hi, he⟩ := lowMixtureLaw_nonneg_integrable_integral μ m n a V t f hf ha ht hp H hH hn
    (lowMixtureMean_integrable μ m n a V t f H hξ)
  refine ⟨hi, he.trans ?_⟩
  simp only [lowMixtureMean, integral_finsetSum _ (fun ξ _ => (hξ ξ).const_mul _), integral_const_mul]

end

def lowMixtureScore {α : Type*} (m n : ℕ) (a V η : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ) (z : α × LowMixtureMarks m n) : ℝ :=
  finiteExperimentScore m n a V η (f z.1) z.2.1 z.2.2

theorem lowMixtureScore_measurable {α : Type*} [MeasurableSpace α]
    (m n : ℕ) (a V η : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) :
    Measurable (lowMixtureScore m n a V η f) := by
  aesop (add safe apply [measurable_from_prod_countable_left, finiteExperimentScore_measurable_comp])

section
variable {α : Type*} [MeasurableSpace α]

theorem lowMixtureIndexKernel_score_centered
    (m n : ℕ) (a V η t : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 < ternaryMass a (f x ξ i) V y)
    (x : α) :
    (∫ z, lowMixtureScore m n a V η f (x, z)
      ∂lowMixtureIndexKernel m n a V t f hf x) = 0 := by
  rw [lowMixtureIndexKernel_integral m n a V t f hf ht
    (fun x ξ i y => (hp x ξ i y).le)]
  unfold lowMixtureMean lowResponseMean lowMixtureScore
  have hc (ξ : Fin m → Fin 3) := finite_experiment_score_centered m n a V η (f x) ξ ha
    (fun y => Finset.prod_pos (fun i _ => hp x ξ i (y i)))
  simp [hc, mul_zero]

/-- Score moments in the augmented law from the per-state conditional energies. -/
theorem lowMixtureScore_facts
    (μ : Measure α) [IsProbabilityMeasure μ] (m n : ℕ) (a V η t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 < ternaryMass a (f x ξ i) V y)
    (hξ : ∀ ξ, Integrable (lowResponseMean m n a V f (fun z => lowMixtureScore m n a V η f z ^ 2) ξ) μ) :
    let P := lowMixtureLaw μ m n a V t f hf
    let S := lowMixtureScore m n a V η f
    MemLp S 2 P ∧ (∫ z, S z ∂P) = 0 ∧ (∫ z, S z ^ 2 ∂P) =
      ∑ ξ, activationProductPrior m t ξ * ∫ x, lowResponseMean m n a V f (fun z => S z ^ 2) ξ x ∂μ := by
  have hq x ξ i y := (hp x ξ i y).le
  let := lowMixtureIndexKernel_markov m n a V t f hf ha ht hq
  let := lowMixtureLaw_probability μ m n a V t f hf ha ht hq
  have hm := lowMixtureScore_measurable m n a V η f hf
  obtain ⟨hi, hE⟩ := lowMixtureLaw_nonneg_moments μ m n a V t f hf ha ht hq _
    (hm.pow_const 2) (fun _ => sq_nonneg _) hξ
  have hS := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 hi
  refine ⟨hS, ?_, hE⟩
  rw [lowMixtureLaw, Measure.integral_compProd (hS.integrable (by norm_num))]
  simp only [lowMixtureIndexKernel_score_centered m n a V η t f hf ha ht hp, integral_zero]

end

end NearlyMinimax
