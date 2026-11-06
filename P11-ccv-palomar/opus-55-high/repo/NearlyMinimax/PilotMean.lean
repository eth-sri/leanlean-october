module

public import NearlyMinimax.PilotFields
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual conditional means of two-pilot bilinear statistics. -/
𝚯
𝚻
namespace NearlyMinimax.PilotFields
𝚩

𝛖
𝛓
𝛌
𝛕

𝗃 𝔓 m w + η ἀ w
def pilotMean (m : W → H) (η : 𝙟₂) (B : 𝘇₁) (z : 𝚎) : ℝ :=
  ∫ w, ⟪𝔓 z.1, B w 𝔓 z.2⟫ ∂M

𝗇 𝔄 B w $ m w
𝗇 𝔅 𝙭₂
𝗃 𝔔 ἀ (M := M)
𝗇 𝔇 𝔔 pilotMean m η B
𝗇 𝔈 η y w
𝗇 𝔉 fun z : 𝗶₁ => 𝘭₂
𝗇 𝔊 𝚇
𝗇 𝔍 ∫ w, ⟪m w, 𝔄⟫ ∂M
𝗇 𝔑 fun w => 𝔄
𝗇 𝔎 𝔔 fluctuation η B 𝔑 𝔑
𝗇 𝔏 𝘯₂
theorem pilotMean_sub_eq m (hmm : Measurable m) (hm : MemLp m 2 M)
    (hmη : Measurable 𝔉)
    (hmB : Measurable 𝔊)
    (hbound : 𝔏)
    (hsym : 𝔅)
    (hx : MemLp (η x) 2 M) (hy : MemLp (η y) 2 M) :
    𝔇 𝖮 - 𝔍 =
      𝔎 𝖮 := by
  have hBm := operatorField_memLp hmB hbound hmm hm
  have hBy := operatorField_memLp hmB hbound (hmη.comp $ measurable_const.prodMk measurable_id ) hy
  have h₀ := inner_integrable hm hBm
  have h₁ := inner_integrable hx hBm
  have h₂ := inner_integrable hy hBm
  have he : (fun w => ⟪𝔓 x, B w $ m w + 𝔈 ⟫) =
       fun w => ⟪m w, 𝔄⟫ + ⟪η x w, 𝔄⟫ +
        ⟪𝔈, 𝔄⟫ + ⟪η x w, B w 𝔈⟫ := by
    funext w
    rw [map_add, inner_add_left, inner_add_right, inner_add_right,
      hsym w (m w) 𝔈, real_inner_comm 𝔄 𝔈]
    ring
  have ha := integral_add ((h₀.add h₁).add h₂) $ inner_integrable hx hBy
  have hb := integral_add (h₀.add h₁) h₂
  have hc := integral_add h₀ h₁
  simp at ha hb hc
  simp only [pilotMean, fluctuation, test, bilinear]
  rw [he, ha, hb, hc]
  ring

𝗇 𝔐 (𝔇 z - 𝔍) ^ 2
𝗃 𝔒 ∫ w, ‖ἀ w‖ ^ 2 ∂M
/-- The deterministic-centered pilot mean has its variance bound derived
from the original universal linear tests. -/
theorem pilotMean_centered_sq_le m (hmm : Measurable m) (hm : MemLp m 2 M)
    (hmη : Measurable 𝔉)
    (hη : 𝗢₁)
    (hmB : Measurable 𝔊)
    (hC : 𝖺₁) (hlam : 𝖺) (hbound : 𝔏)
    (hsym : 𝔅)
    (htest : ∀ v , MemLp v 2 M →
       ∫ x, 𝔔 test η v x ^ 2 ∂μ ≤ lam * 𝔒 v) :
     ∫ z, 𝔐 ∂μ.prod μ ≤
      3 * lam * C ^ 2 * (2 * 𝔒 m +
        ∫ z : 𝗶₁, ‖𝘭₂‖ ^ 2 ∂μ.prod M) := by
  have hBm := operatorField_memLp hmB hbound hmm hm
  have he : (fun z => 𝔐) =ᵐ[μ.prod μ]
       fun z => 𝔎 z ^ 2 := by
    filter_upwards [𝘳₂ $ memLp_sections hη ,
      𝘴₂ $ memLp_sections hη ] with z hx hy
    rw [pilotMean_sub_eq m hmm hm hmη hmB hbound hsym hx hy]
  rw [integral_congr_ae he]
  apply (fluctuation_energy_le hmη hη hmB hC hlam hbound htest hBm hBm).trans
  have hv := operatorField_energy_le hmB hC hbound hmm hm
  nlinarith
