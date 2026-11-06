module

public import NearlyMinimax.PilotMean
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Centered independent pilot fields give the exact deterministic population
mean, as well as genuine L² integrability of the bilinear pilot mean. -/
𝚯
open scoped RealInnerProductSpace ENNReal
namespace NearlyMinimax.PilotFields
𝚩

𝛖
variable [NormedAddCommGroup H] [𝗗₂] [CompleteSpace H]
𝛌
𝛕

𝗃 𝔖 ἀ (M := M)
𝗇 𝔄 ∀ v , MemLp v 2 M → ∫ x, 𝔖 test η v x ^ 2 ∂μ ≤ lam * ∫ w, 𝚌₂ ∂M
𝗇 𝔅 𝗢₁
𝗇 𝔈 Measurable fun z : 𝗶₁ => 𝘭₂
𝗇 𝔉 Measurable 𝚇
𝗇 𝔍 𝘯₂
𝗇 𝔏 ∀ᵐ w ∂M, 𝘦₁
𝗇 𝔓 𝔖 fluctuation η B
theorem fluctuation_mean_zero
    (hmη : 𝔈)
    (hη : 𝔅)
    (hcenter : 𝔏)
    (hmB : 𝔉)
    (hC : 𝖺₁) (hlam : 𝖺) (hbound : 𝔍)
    (htest : 𝔄)
    (hv₁ : MemLp v₁ 2 M) (hv₂ : MemLp v₂ 2 M) :
     ∫ z, 𝔓 v₁ v₂ z ∂μ.prod μ = 0 := by
  have h₁ := (test_memLp_two hη hv₁).integrable 𝖠₄
  have h₂ := (test_memLp_two hη hv₂).integrable 𝖠₄
  have h₃ := (bilinear_memLp_two hmη hη hmB hC hlam hbound htest).integrable
    𝖠₄
  have ha := integral_add ((h₁.comp_fst μ).add $ h₂.comp_snd μ ) h₃
  have hb := integral_add (h₁.comp_fst μ) $ h₂.comp_snd μ
  simp at ha hb
  change ∫ z : 𝚎, test η v₁ z.1 + test η v₂ z.2 +
    bilinear η B z ∂μ.prod μ = 0
  rw [ha, hb, integral_fun_fst, integral_fun_snd,
    test_mean_zero hη hcenter hv₁, test_mean_zero hη hcenter hv₂,
    bilinear_mean_zero hmη hη hcenter hmB hC hlam hbound htest]
  simp

𝗇 𝔇 𝙭₂
𝗇 𝔊 ∫ w, ⟪m w, B w $ m w ⟫ ∂M
𝗇 𝔎 𝔖 pilotMean m η B
𝗇 𝔐 fun w => B w $ m w
𝗇 𝔔 MemLp m 2 M
theorem pilotMean_eq_fluctuation_ae m (hmm : Measurable m) (hm : 𝔔)
    (hmη : 𝔈)
    (hη : 𝔅)
    (hmB : 𝔉)
    (hbound : 𝔍)
    (hsym : 𝔇) :
    𝔎 =ᵐ[μ.prod μ]
       fun z => 𝔓 𝔐
        𝔐 z + 𝔊 := by
  filter_upwards [𝘳₂ $ memLp_sections hη ,
    𝘴₂ $ memLp_sections hη ] with z hx hy
  have he := pilotMean_sub_eq m hmm hm hmη hmB hbound hsym hx hy
  linarith

𝗇 𝔑 pilotMean_eq_fluctuation_ae m hmm hm hmη hη hmB hbound hsym
𝗇 𝔒 fluctuation_memLp_two hmη hη hmB hC hlam hbound htest hBm hBm
theorem pilotMean_memLp_two m (hmm : Measurable m) (hm : 𝔔)
    (hmη : 𝔈)
    (hη : 𝔅)
    (hmB : 𝔉)
    (hC : 𝖺₁) (hlam : 𝖺) (hbound : 𝔍)
    (hsym : 𝔇)
    (htest : 𝔄) :
    MemLp 𝔎 2 $ μ.prod μ := by
  have hBm := operatorField_memLp hmB hbound hmm hm
  exact ((𝔒).add
    $ memLp_const 𝔊 ).ae_eq
      (𝔑).symm

theorem pilotMean_mean_eq m (hmm : Measurable m) (hm : 𝔔)
    (hmη : 𝔈)
    (hη : 𝔅)
    (hcenter : 𝔏)
    (hmB : 𝔉)
    (hC : 𝖺₁) (hlam : 𝖺) (hbound : 𝔍)
    (hsym : 𝔇)
    (htest : 𝔄) :
     ∫ z, 𝔎 z ∂μ.prod μ = 𝔊 := by
  have hBm := operatorField_memLp hmB hbound hmm hm
  rw [integral_congr_ae 𝔑]
  rw [integral_add ((𝔒).integrable
    𝖠₄ ) $ integrable_const _ ,
    fluctuation_mean_zero hmη hη hcenter hmB hC hlam hbound htest hBm hBm]
  simp
