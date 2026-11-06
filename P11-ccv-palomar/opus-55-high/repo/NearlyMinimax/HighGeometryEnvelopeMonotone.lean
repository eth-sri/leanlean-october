module

public import NearlyMinimax.HighCompleteGeometry
public import NearlyMinimax.CompleteSourceSaddleParameters
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The true source activation budget dominates its unbalanced row mass,
and the complete geometry H increases with this budget. -/
𝚫
𝚨
𝚩
set_option maxHeartbeats 300000
𝚬

 set_option hygiene false
𝗇 𝔄 𝚎₁^(n+3)*𝗸
𝗇 𝔅 𝚀₂
theorem completeSourceGeometryEnvelope_mono_total D M R q
    aD bD c0 ell N mu C a rho eta Chi
    (hB1 : 0 ≤ B1) (hB : B1 ≤ B2) n (U : 𝙇) :
    𝔅 B1 n U ≤
      𝔅 B2 n U := by
  rcases n with _|_|_|n
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · change (if n+3 ≤ D then _ else 𝔄*(B1+1)^2) ≤
       if n+3 ≤ D then _ else 𝔄*(B2+1)^2
    split_ifs
    · exact le_rfl
    · exact mul_le_mul_of_nonneg_left ((sq_le_sq₀  𝖡₄  𝖡₄ ).mpr 𝖡₄ ) 𝖠₃

 theorem rowMass_le_balanced_source_activity [Fintype I]
    [𝙪] (C : ModelConstants d)
    (R : 𝗽) (hR : 0 ≤ highRowTotalMass R.rowMass) :
    highRowTotalMass R.rowMass ≤ 𝗰₁ := by
  apply (le_div_iff₀ 𝘗₁).mpr
  exact mul_le_of_le_one_right hR (highCenterMix_mem C).2.le
