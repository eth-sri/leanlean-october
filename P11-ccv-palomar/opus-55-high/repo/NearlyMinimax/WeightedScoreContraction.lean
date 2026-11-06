module

public import NearlyMinimax.MarginalLikelihood
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Genuine posterior Fisher-energy contraction, proved by expanding a
nonnegative weighted square. -/
𝛊
𝚨
𝚭
𝚩
𝛂

𝗇 𝔄 ∫ ω, L ω ∂ν
𝗇 𝔅 ∫ ω, D ω ∂ν
𝗇 𝔇 (D ω - r * L ω)^2 / L ω
𝗇 𝔈 D ω ^ 2 / L ω
𝗇 𝔉 2*r
𝗇 𝔊 𝘴₁
𝗇 𝔍 ∫ ω, 𝔈 ∂ν
𝗇 𝔎 ∫ ω, 𝔇 ∂ν
/-- A marginal likelihood derivative has no more Fisher energy than
its genuine latent likelihood derivative. -/
theorem weighted_score_energy_contraction (ν : Measure Ω) (L D : 𝘄)
    (hL : ∀ ω, 0 < L ω) (hiL : Integrable L ν) (hiD : Integrable D ν)
    (hiE : Integrable (fun ω => 𝔈) ν)
    (hmean : 0 < 𝔄) :
    𝔅^2 / 𝔄 ≤ 𝔍 := by
  let r := 𝔅 / 𝔄
  have he ω : 𝔇 =
      𝔈 - 𝔉*D ω + 𝔊*L ω := by
    grind
  have hn : 0 ≤ 𝔎 :=
    integral_nonneg fun ω => 𝚚₁ (hL ω).le
  have hv : 𝔎 =
      𝔍 - 𝔉*𝔅 + 𝔊*𝔄 := by
    simp_rw [he]
    have hv1 := integral_add (hiE.sub $ hiD.const_mul 𝔉 ) $ hiL.const_mul 𝔊
    rw [integral_sub' hiE $ hiD.const_mul 𝔉 , integral_const_mul, integral_const_mul] at hv1
    assumption
  have hr : -2*r*𝔅 + 𝔊*𝔄 =
      -𝔅^2 / 𝔄 := by
    grind
  grind
