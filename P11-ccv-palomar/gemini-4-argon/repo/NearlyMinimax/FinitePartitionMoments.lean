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
  rw [measureReal_def, Measure.map_apply hlabel (measurableSet_singleton c)]
  rfl

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

theorem sameLabelKernel_row (x ) :
    (∫ y, sameLabelKernel label (x, y) ∂μ) = μ.real (label ⁻¹' {label x}) := by
  have he : (fun y => sameLabelKernel label (x, y)) =
      (label ⁻¹' {label x}).indicator (fun _ => 1) := by
    funext y
    simp [sameLabelKernel, Set.indicator, eq_comm]
  rw [he, integral_indicator ((measurableSet_singleton _).preimage hlabel)]
  simp

theorem sameLabelKernel_integral :
    (∫ z, sameLabelKernel label z ∂μ.prod μ) = ∑ c, μ.real (label ⁻¹' {c}) ^ 2 := by
  rw [integral_prod _ ((sameLabelKernel_memLp μ label hlabel).integrable (by norm_num))]
  simp_rw [sameLabelKernel_row μ label hlabel]
  rw [finite_label_integral μ label hlabel (fun c => μ.real (label ⁻¹' {c}))]
  simp only [pow_two]

theorem sameLabelKernel_square_integral :
    (∫ z, (sameLabelKernel label z) ^ 2 ∂μ.prod μ) = ∑ c, μ.real (label ⁻¹' {c}) ^ 2 := by
  have he : (fun z => (sameLabelKernel label z) ^ 2) = sameLabelKernel label := by
    funext z
    unfold sameLabelKernel
    split_ifs <;> norm_num
  rw [he, sameLabelKernel_integral μ label hlabel]

theorem sameLabelKernel_row_square_integral :
    (∫ x, (∫ y, sameLabelKernel label (x, y) ∂μ) ^ 2 ∂μ) =
      ∑ c, μ.real (label ⁻¹' {c}) ^ 3 := by
  simp_rw [sameLabelKernel_row μ label hlabel]
  rw [finite_label_integral μ label hlabel (fun c => μ.real (label ⁻¹' {c}) ^ 2)]
  apply Finset.sum_congr rfl
  intro c hc
  ring

end Partition

theorem finite_probability_second_moment_le  [Fintype B]
    (p : B → ℝ) (cap : ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1)
    (hcap : ∀ c, p c ≤ cap) : ∑ c, p c ^ 2 ≤ cap := by
  calc
    _ ≤ ∑ c, cap * p c := by
      apply Finset.sum_le_sum
      intro c hc
      nlinarith [mul_le_mul_of_nonneg_right (hcap c) (hp c)]
    _ = cap := by rw [← Finset.mul_sum, hsum, mul_one]

theorem finite_probability_third_moment_le  [Fintype B]
    (p : B → ℝ) (cap : ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1)
    (hcap : ∀ c, p c ≤ cap) (hc : 0 ≤ cap) : ∑ c, p c ^ 3 ≤ cap ^ 2 := by
  calc
    _ ≤ cap * ∑ c, p c ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro c hmem
      nlinarith [mul_le_mul_of_nonneg_right (hcap c) (sq_nonneg (p c))]
    _ ≤ cap * cap := mul_le_mul_of_nonneg_left
      (finite_probability_second_moment_le p cap hp hsum hcap) hc
    _ = cap ^ 2 := by ring

def regularGridCollisionMass  (θ : RegressionParameter d) (k ) (hk : 0 < k) : ℝ :=
  ∑ c, regularGridProbability θ k hk c ^ 2

theorem regularGridCollisionMass_lower {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    1 / ↑k ^ d ≤ regularGridCollisionMass θ k hk := by
  have h_partitionPairMass_lower : 1 ≤ partitionPairMass (regularGridProbability θ k hk) := by
    have hsum  := regularGridProbability_sum C θ hθ k hk
    simpa [partitionPairMass, hsum] using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := regularGridProbability θ k hk))
  have hmass := h_partitionPairMass_lower
  simp only [partitionPairMass, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at hmass
  exact (div_le_iff₀ (pow_pos (by exact_mod_cast hk) d)).2 (by simpa only [mul_comm, regularGridCollisionMass] using hmass)

theorem regularGridCollisionMass_upper  (C : ModelConstants d)
    (θ ) (hθ : Admissible C θ) (k hk) :
    regularGridCollisionMass θ k hk ≤ C.densityUpper / ↑k ^ d :=
  finite_probability_second_moment_le _ _ (regularGridProbability_nonneg θ k hk)
    (regularGridProbability_sum C θ hθ k hk) (regularGridProbability_cap C θ hθ k hk)

end NearlyMinimax
