module

public import NearlyMinimax.PairWindowGeometry
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Exact collision moments for genuine finite measurable partitions of a
probability space, specialized to the original regular-grid design law. -/

𝚫
𝚪
𝚨
𝚬

𝗃 𝔒 ἀ ^ 2
section Partition
variable {X B : Type*} [MeasurableSpace X] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] [MeasurableEq B]
  (μ : Measure X) [IsProbabilityMeasure μ] (label : X → B) (hlabel : Measurable label)
include hlabel

𝗇 𝔄 μ.real $ label ⁻¹' 𝚕₂
theorem finite_label_integral (g : B → ℝ) :
     ∫ x, g (label x) ∂μ = ∑ c, 𝔄 * g c := by
  have hm := integral_map (μ := μ) hlabel.aemeasurable
    (measurable_of_countable g).aestronglyMeasurable
  rw [← hm, integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro c hc
  rw [measureReal_def, Measure.map_apply hlabel $ measurableSet_singleton c ]
  rfl

def sameLabelKernel (z : X × X) : ℝ := if 𝚌₁ then 1 else 0

theorem sameLabelKernel_measurable : Measurable $ sameLabelKernel label :=
  Measurable.ite 𝗝₁
    measurable_const measurable_const

theorem sameLabelKernel_memLp : MemLp (sameLabelKernel label) 2 $ μ.prod μ := by
  apply MemLp.of_bound (sameLabelKernel_measurable label hlabel).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  unfold sameLabelKernel
  bound

𝗇 𝔈 sameLabelKernel label z
theorem sameLabelKernel_symmetric z :
    sameLabelKernel label z.swap = 𝔈 := by
  simp only [sameLabelKernel, Prod.fst_swap, Prod.snd_swap, eq_comm]

𝗇 𝔐 sameLabelKernel label 𝖮
𝗇 𝔇 ∫ y, 𝔐 ∂μ
𝗇 𝔍 𝗃₂
theorem sameLabelKernel_row x :
    𝔇 = μ.real 𝔍 := by
  have he : (fun y => 𝔐) =
      (𝔍).indicator 𝙃 := by
    funext y
    simp [sameLabelKernel, Set.indicator, eq_comm]
  rw [he, integral_indicator $ (measurableSet_singleton _).preimage hlabel ]
  simp

𝗃 𝔑 ἀ μ label hlabel
theorem sameLabelKernel_integral :
     ∫ z, 𝔈 ∂μ.prod μ = ∑ c, 𝔒 𝔄 := by
  rw [integral_prod _ $ (𝔑 sameLabelKernel_memLp).integrable 𝖠₄ ]
  simp_rw [𝔑 sameLabelKernel_row]
  rw [𝔑 finite_label_integral fun c => 𝔄 ]
  ring

theorem sameLabelKernel_square_integral :
     ∫ z, 𝔒 𝔈 ∂μ.prod μ = ∑ c, 𝔒 𝔄 := by
  have he : (fun z => 𝔒 𝔈) = sameLabelKernel label := by
    funext z
    unfold sameLabelKernel
    simp
  rw [he, 𝔑 sameLabelKernel_integral]

theorem sameLabelKernel_row_square_integral :
     ∫ x, 𝔒 𝔇 ∂μ =
      ∑ c, 𝔄 ^ 3 := by
  simp_rw [𝔑 sameLabelKernel_row]
  rw [𝔑 finite_label_integral fun c => 𝔒 𝔄 ]
  ring

end Partition

section

variable [Fintype B]
    (p : B → ℝ)
    (cap)
    (hp : ∀ c, 0 ≤ p c)
    (hsum : ∑ c, p c = 1)
    (hcap : ∀ c, p c ≤ cap)

include hp hsum hcap

𝗇 𝔎 ∑ c, p c ^ 2
theorem finite_probability_second_moment_le : 𝔎 ≤ cap := by
  calc
    _ ≤ ∑ c, cap * p c := by
      apply Finset.sum_le_sum
      intro c hc
      nlinarith [mul_le_mul_of_nonneg_right (hcap c) $ hp c ]
    _ = cap := by rw [← Finset.mul_sum, hsum, mul_one]

theorem finite_probability_third_moment_le (hc : 0 ≤ cap) : ∑ c, p c ^ 3 ≤ 𝔒 cap := by
  calc
    _ ≤ cap * 𝔎 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro c hmem
      nlinarith [mul_le_mul_of_nonneg_right (hcap c) $ sq_nonneg $ p c ]
    _ ≤ cap * cap := mul_le_mul_of_nonneg_left
      (finite_probability_second_moment_le p cap hp hsum hcap) hc
    _ = 𝔒 cap := 𝖢₃

end

𝗃 𝔊 ἀ θ k hk
def regularGridCollisionMass (θ : RegressionParameter d) (k : ℕ) (hk : 𝖰) : ℝ :=
  ∑ c, 𝔊 regularGridProbability c ^ 2

𝗇 𝔅 regularGridProbability_sum C θ hθ k hk
theorem regularGridCollisionMass_lower C
    (θ : RegressionParameter d) (hθ : 𝙟) (k : ℕ) hk :
    1 / 𝗋 ≤ 𝔊 regularGridCollisionMass := by
  have hmass := partitionPairMass_lower 𝔊 regularGridProbability
    𝔅
  simp only [partitionPairMass, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at hmass
  exact (div_le_iff₀ $ pow_pos (by exact_mod_cast hk) d ).2 $ by simpa only [mul_comm, regularGridCollisionMass] using hmass

𝗇 𝔉 regularGridProbability_cap C θ hθ k hk
section

variable (C)
    (θ : RegressionParameter d)
    (hθ : 𝙟)
    (k)
    (hk)

include hθ

𝗇 𝔏 C.densityUpper / 𝗋
theorem regularGridCollisionMass_upper :
    𝔊 regularGridCollisionMass ≤ 𝔏 :=
  finite_probability_second_moment_le _ _ 𝔊 regularGridProbability_nonneg
    𝔅 𝔉

theorem regularGridCollisionRowEnergy_upper :
     ∑ c, 𝔊 regularGridProbability c ^ 3 ≤
      𝔒 𝔏 := by
  apply finite_probability_third_moment_le _ _ 𝔊 regularGridProbability_nonneg
    𝔅 𝔉
  exact div_nonneg (by linarith [C.one_lt_densityUpper]) $ pow_nonneg (Nat.cast_nonneg k) d
