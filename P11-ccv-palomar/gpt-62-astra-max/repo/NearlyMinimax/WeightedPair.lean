module

public import NearlyMinimax.PairLocalization


@[expose] public section

/-! Symmetrized, weighted, order-two pair statistics. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax.PairUStatistic
set_option backward.isDefEq.respectTransparency false

variable {E I : Type*} [MeasurableSpace E] [MeasurableSpace I]
variable [MeasurableSingletonClass I]
variable {μ : Measure E} [IsProbabilityMeasure μ]

def weightedSymmetrization (weight : ℝ) (G : E × E → ℝ) (z : E × E) : ℝ :=
  weight / 4 * (G z + G z.swap)

section
variable (weight : ℝ) {label : E → I} {G : E × E → ℝ} (hG : MemLp G 2 (μ.prod μ))

theorem weightedSymmetrization_measurable
    (hmG : Measurable G) : Measurable (weightedSymmetrization weight G) :=
  (hmG.add (hmG.comp measurable_swap)).const_mul _

include hG in
theorem weightedSymmetrization_memLp : MemLp (weightedSymmetrization weight G) 2 (μ.prod μ) :=
  (hG.add (hG.comp_measurePreserving Measure.measurePreserving_swap)).const_mul _

include hG in
theorem weightedSymmetrization_mean :
    (∫ z, weightedSymmetrization weight G z ∂μ.prod μ) =
      weight / 2 * ∫ z, G z ∂μ.prod μ := by
  have ha := integral_add (hG.integrable (by norm_num)) ((hG.comp_measurePreserving Measure.measurePreserving_swap).integrable (by norm_num))
  simp at ha
  simp [weightedSymmetrization]
  rw [integral_const_mul, ha, integral_prod_swap G]
  ring

include hG in
theorem weightedSymmetrization_energy_le :
    (∫ z, weightedSymmetrization weight G z ^ 2 ∂μ.prod μ) ≤
      weight ^ 2 / 4 * ∫ z, G z ^ 2 ∂μ.prod μ := by
  have h₁ := hG.integrable_sq
  have h₂ := (hG.comp_measurePreserving Measure.measurePreserving_swap).integrable_sq
  calc
    _ ≤ ∫ z, weight ^ 2 / 8 * (G z ^ 2 + G z.swap ^ 2) ∂μ.prod μ := by
      apply integral_mono (weightedSymmetrization_memLp weight hG).integrable_sq
        ((h₁.add h₂).const_mul _)
      intro z
      have hs : (G z + G z.swap) ^ 2 ≤ 2 * (G z ^ 2 + G z.swap ^ 2) := by
        nlinarith [sq_nonneg (G z - G z.swap)]
      dsimp [weightedSymmetrization]
      nlinarith
    _ = _ := by
      have ha := integral_add h₁ h₂
      simp at ha
      rw [integral_const_mul, ha, integral_prod_swap (fun z => G z ^ 2)]
      ring

theorem weightedSymmetrization_supported (hsupport : ∀ x y, label x ≠ label y → G (x, y) = 0) :
    ∀ x y, label x ≠ label y → weightedSymmetrization weight G (x, y) = 0 := by
  grind [weightedSymmetrization]

end

theorem weighted_pair_centered_sq_le {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {n : ℕ} (hn : 2 ≤ n)
    {X : Fin n → Ω → E} (hind : ProbabilityTheory.iIndepFun X ν)
    (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {label : E → I} (hlabel : Measurable label)
    {G : E × E → ℝ} (hmG : Measurable G) (hG : MemLp G 2 (μ.prod μ))
    (hsupport : ∀ x y, label x ≠ label y → G (x, y) = 0)
    {weight cap P : ℝ} (hweight : 0 < weight) (hcap : 0 ≤ cap)
    (hmass : ∀ i, μ.real (label ⁻¹' {i}) ≤ cap) (hP : weight * cap ≤ P) :
    (∫ x, (pairAverage n (weightedSymmetrization weight G) (fun i => X i x) -
      weight / 2 * ∫ z, G z ∂μ.prod μ) ^ 2 ∂ν) ≤
      (P / n + weight / (2 * n * (n - 1 : ℕ))) *
        (weight * ∫ z, G z ^ 2 ∂μ.prod μ) := by
  have hv := partition_pairAverage_centered_sq_le hn hind hX hlabel
    (weightedSymmetrization_measurable weight hmG) (weightedSymmetrization_memLp weight hG)
    (by simp [weightedSymmetrization, add_comm]) (weightedSymmetrization_supported weight hsupport)
    hmass
  rw [weightedSymmetrization_mean weight hG] at hv
  apply hv.trans
  apply (mul_le_mul_of_nonneg_left (weightedSymmetrization_energy_le weight hG) (by positivity)).trans
  have hn0 : 0 < (n : ℝ) := by positivity
  have henergy : 0 ≤ ∫ z, G z ^ 2 ∂μ.prod μ := by positivity
  have hscale : (4 / n * cap + 2 / (n * (n - 1 : ℕ))) * (weight ^ 2 / 4) =
      (weight * cap / n + weight / (2 * n * (n - 1 : ℕ))) * weight := by
    field_simp
    <;> ring
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (add_le_add_right (div_le_div_of_nonneg_right hP hn0.le)
        (weight / (2 * n * (n - 1)))) hweight.le) henergy
  nlinarith

end NearlyMinimax.PairUStatistic
