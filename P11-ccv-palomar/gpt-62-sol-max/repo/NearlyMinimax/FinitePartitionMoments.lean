module

public import NearlyMinimax.PairWindowGeometry


@[expose] public section

/-! Exact collision moments for genuine finite measurable partitions of a
probability space, specialized to the original regular-grid design law. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
attribute [local instance] Classical.propDecidable

section Partition
variable {X B : Type*} [MeasurableSpace X] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] [MeasurableEq B]
  (μ : Measure X) [IsProbabilityMeasure μ] (label : X → B) (hlabel : Measurable label)
include hlabel

theorem finite_label_integral (g : B → ℝ) :
    (∫ x, g (label x) ∂μ) = ∑ c, μ.real (label ⁻¹' {c}) * g c := by
  have hm := integral_map (μ := μ) hlabel.aemeasurable
    (measurable_of_countable g).aestronglyMeasurable
  rw [← hm, integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro c hc
  simp [measureReal_def, Measure.map_apply hlabel (measurableSet_singleton c)]

def sameLabelKernel (z : X × X) : ℝ := if label z.1 = label z.2 then 1 else 0

theorem sameLabelKernel_measurable : Measurable (sameLabelKernel label) :=
  Measurable.ite (measurableSet_eq_fun (hlabel.comp measurable_fst) (hlabel.comp measurable_snd))
    measurable_const measurable_const

theorem sameLabelKernel_memLp : MemLp (sameLabelKernel label) 2 (μ.prod μ) := by
  apply MemLp.of_bound (sameLabelKernel_measurable label hlabel).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro z
  unfold sameLabelKernel
  split_ifs <;> norm_num

theorem sameLabelKernel_symmetric (z : X × X) :
    sameLabelKernel label z.swap = sameLabelKernel label z := by
  simp only [sameLabelKernel, Prod.fst_swap, Prod.snd_swap, eq_comm]

theorem sameLabelKernel_row (x : X) :
    (∫ y, sameLabelKernel label (x, y) ∂μ) = μ.real (label ⁻¹' {label x}) := by
  have he : (fun y => sameLabelKernel label (x, y)) =
      (label ⁻¹' {label x}).indicator (fun _ => (1 : ℝ)) := by
    funext y
    simp [sameLabelKernel, Set.indicator, eq_comm]
  simp [he, integral_indicator ((measurableSet_singleton _).preimage hlabel)]

theorem sameLabelKernel_integral :
    (∫ z, sameLabelKernel label z ∂μ.prod μ) = ∑ c, μ.real (label ⁻¹' {c}) ^ 2 := by
  simp [integral_prod _ ((sameLabelKernel_memLp μ label hlabel).integrable (by norm_num)), sameLabelKernel_row μ label hlabel, finite_label_integral μ label hlabel (fun c => μ.real (label ⁻¹' {c}))] <;> ring

theorem sameLabelKernel_square_integral :
    (∫ z, (sameLabelKernel label z) ^ 2 ∂μ.prod μ) = ∑ c, μ.real (label ⁻¹' {c}) ^ 2 := by
  have he : (fun z => (sameLabelKernel label z) ^ 2) = sameLabelKernel label := by
    funext z
    unfold sameLabelKernel
    simp
  rw [he, sameLabelKernel_integral μ label hlabel]

end Partition

section
variable {B : Type*} [Fintype B]
    (p : B → ℝ) (cap : ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1)
    (hcap : ∀ c, p c ≤ cap)
include hp hsum hcap

theorem finite_probability_second_moment_le : ∑ c, p c ^ 2 ≤ cap := by
  calc
    _ ≤ ∑ c, cap * p c := by
      apply Finset.sum_le_sum
      intro c hc
      nlinarith [mul_le_mul_of_nonneg_right (hcap c) (hp c)]
    _ = cap := by rw [← Finset.mul_sum, hsum, mul_one]

end

def regularGridCollisionMass {d : ℕ} (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k) : ℝ :=
  ∑ c, regularGridProbability θ k hk c ^ 2

section
variable {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k)
include hθ

theorem regularGridCollisionMass_lower :
    1 / (k : ℝ) ^ d ≤ regularGridCollisionMass θ k hk := by
  have hmass := partitionPairMass_lower (regularGridProbability θ k hk)
    (regularGridProbability_sum C θ hθ k hk)
  simp only [partitionPairMass, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at hmass
  have hkr : 0 < (k : ℝ) := by positivity
  exact (div_le_iff₀ (pow_pos hkr d)).2 (by simpa only [mul_comm, regularGridCollisionMass] using hmass)

theorem regularGridCollisionMass_upper :
    regularGridCollisionMass θ k hk ≤ C.densityUpper / (k : ℝ) ^ d :=
  finite_probability_second_moment_le _ _ (regularGridProbability_nonneg θ k hk)
    (regularGridProbability_sum C θ hθ k hk) (regularGridProbability_cap C θ hθ k hk)

end

end NearlyMinimax
