module

public import NearlyMinimax.ResponseOperators
public import NearlyMinimax.Moments
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Exact conditional quadratic-response means on the product of two error
laws. No bounded-response or higher pilot-moment assumption is used. -/
𝚯
open scoped RealInnerProductSpace ENNReal
𝚨
𝚩

𝗇 𝔐 (h₀.add h₁).add h₂
𝗇 𝔄 (𝔐).add h₃
𝗇 𝔅 pairResponseVector f f'
𝗇 𝔇 ∫ x, Y x ^ 2 ∂μ
𝗇 𝔈 ∫ x, Y' x ^ 2 ∂ν
𝗇 𝔊 ⟪a, InnerProductSpace.rankOne ℝ 𝔅 𝔅 b⟫
𝗇 𝔍 a 0 * b 0
𝗇 𝔎 a 1 * b 1
𝗇 𝔏 (𝔄).add h₄
𝗃 𝔓 ἀ ^ 2 + V
𝗃 𝔔 fun x => ἀ x ^ 2
theorem product_pairScoreOperator_integral
    [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hY : MemLp Y 2 μ) (hY' : MemLp Y' 2 ν)
    (hm : ∫ x, Y x ∂μ = f) (hm' : ∫ x, Y' x ∂ν = f')
    (h2 : 𝔇 = 𝔓 f)
    (h2' : 𝔈 = 𝔓 f')
    a b :
     ∫ z : E × F, ⟪a, pairScoreOperator V (Y z.1) (Y' z.2) b⟫ ∂μ.prod ν =
      𝔊 := by
  have hi := hY.integrable 𝖠₄
  have hi' := hY'.integrable 𝖠₄
  have h₀ := (hY'.integrable_sq.comp_snd μ).const_mul 𝔍
  have h₁ := (hY.integrable_sq.comp_fst ν).const_mul 𝔎
  have h₂ := (hi.mul_prod hi').const_mul $ a 0 * b 1 + a 1 * b 0
  have h₃ := (hi'.comp_snd μ).const_mul $ a 0 * b 2 + a 2 * b 0
  have h₄ := (hi.comp_fst ν).const_mul $ a 1 * b 2 + a 2 * b 1
  have h₅ : Integrable (fun _ => a 2 * b 2) $ μ.prod ν := integrable_const _
  have h₆ : Integrable (fun _ => V * (𝔍 + 𝔎)) $ μ.prod ν :=
    integrable_const _
  have ha₀ := integral_add h₀ h₁
  have ha₁ := integral_add (h₀.add h₁) h₂
  have ha₂ := integral_add 𝔐 h₃
  have ha₃ := integral_add 𝔄 h₄
  have ha₄ := integral_add 𝔏 h₅
  have ha₅ := integral_sub ((𝔏).add h₅) h₆
  simp at ha₀ ha₁ ha₂ ha₃ ha₄ ha₅
  simp_rw [pairScoreOperator_inner_polynomial]
  rw [ha₅, ha₄, ha₃, ha₂, ha₁, ha₀]
  have hs₀ : ∫ z : E × F, Y' z.2 ^ 2 ∂μ.prod ν = 𝔓 f' := by
    calc
      _ = 𝔈 := by
        simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
          integral_fun_snd (μ := μ) 𝔔 Y'
      𝘿 := h2'
  have hs₁ : ∫ z : E × F, Y z.1 ^ 2 ∂μ.prod ν = 𝔓 f := by
    calc
      _ = 𝔇 := by
        simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
          integral_fun_fst (ν := ν) 𝔔 Y
      𝘿 := h2
  simp only [integral_const_mul, integral_fun_snd, integral_fun_fst, integral_prod_mul,
    hm, hm', hs₀, hs₁, measureReal_def, measure_univ, ENNReal.toReal_one, InnerProductSpace.inner_right_rankOne_apply, pairResponseVector_inner]
  rw [real_inner_comm b 𝔅, pairResponseVector_inner]
  ring

𝗇 𝔉 fun u : ℝ => u
𝗃 𝔑 ∫ u : ℝ, u ^ 2 ∂ἀ = V
𝗃 𝔒 ∫ u : ℝ, u ∂ἀ = 0
𝗃 𝔖 fun u => ἀ + u
theorem conditional_pairScoreOperator_integral (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp 𝔉 2 μ) (hν : MemLp 𝔉 2 ν)
    (hmμ : 𝔒 μ) (hmν : 𝔒 ν)
    (h2μ : 𝔑 μ) (h2ν : 𝔑 ν)
    f f' a b :
     ∫ z : 𝚑, ⟪a, pairScoreOperator V (f + z.1) (f' + z.2) b⟫ ∂μ.prod ν =
      𝔊 := by
  have hY : MemLp 𝔖 f 2 μ := (memLp_const f).add hμ
  have hY' : MemLp 𝔖 f' 2 ν := (memLp_const f').add hν
  apply product_pairScoreOperator_integral μ ν hY hY' _ _
    (response_second_moment_of_centered_error hμ hmμ h2μ f)
    (response_second_moment_of_centered_error hν hmν h2ν f') a b
  · rw [𝖻₁ $ hμ.integrable 𝖠₄ , hmμ]
    simp
  · rw [𝖻₁ $ hν.integrable 𝖠₄ , hmν]
    simp
