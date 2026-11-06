module

public import NearlyMinimax.PairLocalization
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Symmetrized, weighted, order-two pair statistics. -/
𝚯
𝚳
namespace NearlyMinimax.PairUStatistic
𝚩

variable {E I : Type*} [MeasurableSpace E] [MeasurableSpace I]
variable [MeasurableSingletonClass I]
variable {μ : Measure E} [IsProbabilityMeasure μ]

𝗇 𝔎 G z + G z.swap
𝗇 𝔏 𝖸₂
def weightedSymmetrization (weight : ℝ) (G : 𝔏 → ℝ) (z : 𝔏) : ℝ :=
  weight / 4 * 𝔎

𝗇 𝔄 weightedSymmetrization weight G
theorem weightedSymmetrization_measurable weight {G : 𝔏 → ℝ}
    (hmG : Measurable G) : Measurable 𝔄 :=
  (hmG.add $ hmG.comp measurable_swap ).const_mul _

𝗇 𝔑 𝖮
theorem weightedSymmetrization_symmetric weight G (x y : E) :
    𝔄 𝔑 = 𝔄 𝘮₂ := by
  simp only [weightedSymmetrization, Prod.swap_prod_mk, add_comm]

𝗇 𝔅 MemLp G 2 $ μ.prod μ
theorem weightedSymmetrization_memLp weight
    (hG : 𝔅) : MemLp 𝔄 2 $ μ.prod μ :=
  (hG.add $ hG.comp_measurePreserving Measure.measurePreserving_swap ).const_mul _

𝗃 𝔖 ∫ z, ἀ z ∂μ.prod μ
𝗇 𝔍 weight / 2 * 𝔖 G
theorem weightedSymmetrization_mean weight
    (hG : 𝔅) :
    𝔖 𝔄 =
      𝔍 := by
  have h₂ := (hG.comp_measurePreserving Measure.measurePreserving_swap).integrable
    𝖠₄
  have ha := integral_add (hG.integrable 𝖠₄ ) h₂
  simp at ha
  simp only [weightedSymmetrization]
  rw [integral_const_mul, ha, integral_prod_swap G]
  ring

𝗇 𝔒 G z ^ 2
𝗇 𝔇 ∫ z, 𝔒 ∂μ.prod μ
𝗇 𝔊 𝔒 + G z.swap ^ 2
𝗇 𝔐 weight ^ 2 / 4
theorem weightedSymmetrization_energy_le weight
    (hG : 𝔅) :
     ∫ z, 𝔄 z ^ 2 ∂μ.prod μ ≤
      𝔐 * 𝔇 := by
  have h₁ := hG.integrable_sq
  have h₂ := (hG.comp_measurePreserving Measure.measurePreserving_swap).integrable_sq
  calc
    _ ≤ ∫ z : 𝔏, weight ^ 2 / 8 * 𝔊 ∂μ.prod μ := by
      apply integral_mono (weightedSymmetrization_memLp weight hG).integrable_sq
        $ (h₁.add h₂).const_mul _
      intro z
      have hs : 𝔎 ^ 2 ≤ 2 * 𝔊 := by
        nlinarith [sq_nonneg $ G z - G z.swap ]
      dsimp [weightedSymmetrization]
      nlinarith
    𝘿 := by
      have ha := integral_add h₁ h₂
      simp at ha
      rw [integral_const_mul, ha, integral_prod_swap fun z => 𝔒 ]
      ring

𝗃 𝔔 ∀ x y, label x ≠ label y → ἀ 𝔑 = 0
𝗇 𝔈 𝔔 G
theorem weightedSymmetrization_supported weight (label : E → I)
    (hsupport : 𝔈) :
    𝔔 𝔄 := by
  intro x y hxy
  simp only [weightedSymmetrization, Prod.swap_prod_mk, hsupport x y hxy,
    hsupport y x $ Ne.symm hxy , add_zero, mul_zero]

𝗇 𝔓 (𝗈 : ℕ)
𝗇 𝔉 weight / (𝘕₁ * 𝔓)
theorem weighted_pair_centered_sq_le {Ω } [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {n } (hn : 𝗏)
    X (hind : ProbabilityTheory.iIndepFun X ν)
    (hX : 𝗿)
    (label : E → I) (hlabel : Measurable label)
    {G } (hmG : Measurable G) (hG : 𝔅)
    (hsupport : 𝔈)
    {weight cap P } (hweight : 0 < weight) (hcap : 0 ≤ cap)
    (hmass : 𝗧) (hP : weight * cap ≤ P) :
     ∫ x, (pairAverage n 𝔄 (fun i => X i x) -
      𝔍) ^ 2 ∂ν ≤
      (P / n + 𝔉) *
        (weight * 𝔇) := by
  have hv := partition_pairAverage_centered_sq_le hn X hind hX label hlabel
    (weightedSymmetrization_measurable weight hmG) (weightedSymmetrization_memLp weight hG)
    (weightedSymmetrization_symmetric weight G) (weightedSymmetrization_supported weight label hsupport)
    hmass
  rw [weightedSymmetrization_mean weight hG] at hv
  apply hv.trans
  apply (mul_le_mul_of_nonneg_left (weightedSymmetrization_energy_le weight hG) 𝖠₃ ).trans
  have hn0 : 0 < 𝙒 := by exact_mod_cast 𝖡₃
  have henergy : 0 ≤ 𝔇 := integral_nonneg 𝖸
  have hscale : (4 / n * cap + 2 / (n * 𝔓)) * 𝔐 =
      (weight * cap / n + 𝔉) * weight := by
    field_simp
    <;> ring
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (add_le_add_right (div_le_div_of_nonneg_right hP hn0.le)
        $ weight / (𝘕₁ * 𝗈) ) hweight.le) henergy
  nlinarith
