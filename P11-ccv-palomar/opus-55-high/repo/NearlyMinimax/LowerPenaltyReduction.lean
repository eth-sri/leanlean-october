module

public import NearlyMinimax.LowerRawCostReduction
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! The genuine mass-exception penalty is negligible compared with the
squared lower saddle scale. Constants are fixed before any model domain. -/
𝚷
𝚶
𝚨
𝚭
𝚩

𝗇 𝔄 𝘦₂
𝗇 𝔅 q/(DV^2+1)
𝗇 𝔇 DV^2
𝗇 𝔈 cm^2/(8*Cmgf)
𝗃 𝔐 ἀ s d
𝗇 𝔉 rateScale 𝔐 rateExponent (𝔐 stretchConstant 𝔄) 𝔐 lowerLogPower x
𝗇 𝔊 𝔐 lowerSaddleCoefficient 𝔄
𝗇 𝔍 𝔐 lowerSaddleTheta 𝔄
𝗇 𝔎 ctr/(3*CG)
𝗃 𝔏 0 < ἀ
/-- The exact numeric lower envelope, after the true tilted exceptional
penalty, dominates a fixed positive multiple of the manuscript's squared
scale. No statistical risk or desired-rate premise is used. -/
theorem eventually_actual_lowerSaddle_penalized_rate_square
    {s d a b cf CG ctr cm Cmgf DV }
    (hs : 𝚊₁) (hd : 𝚄 < d) (ha : 𝔏 a) (hab : 𝙭)
    (hcf : 𝔏 cf) (hCG : 𝔏 CG) (hctr : 𝔏 ctr)
    (hcm : 𝔏 cm) (hCmgf : 𝔏 Cmgf) C :
    ∃ c , 𝔏 c ∧ ∀ᶠ x : ℝ in atTop,
      let m := 𝔊
      let θ := 𝔍
      let τM := 𝙉₂
      (c*𝔉)^2 ≤
      𝔎* 𝔐 lowerSaddleRisk m θ C cf τM x ^2-
        𝔇*lowerSaddleExceptionalTail d m θ C 𝔈 x := by
  obtain ⟨c₀,A,hc₀,hA,hbracket⟩ := actual_lowerSaddleRisk_rate_bracket hs hd ha hab hcf C
  let α := 𝔎
  have hα : 𝔏 α := 𝖠₃
  let q := α*c₀^2/2
  have hq : 𝔏 q := 𝖠₃
  let c := Real.sqrt q
  have htol : 𝔏 𝔅 := 𝖠₃
  have ht := (actual_lowerSaddle_exceptionalTail_over_Psi_tends_zero
    hs hd ha hab hcm hCmgf C).eventually $ eventually_lt_nhds htol
  refine ⟨c, Real.sqrt_pos.mpr hq ,?_⟩
  filter_upwards [hbracket,ht] with x hb hx
  let S := 𝔉
  let R := 𝔐 lowerSaddleRisk 𝔊
    𝔍 C cf 𝙉₂ x
  let ε := lowerSaddleExceptionalTail d 𝔊
    𝔍 C 𝔈 x
  have hS : 𝔏 S := rateScale_pos ..
  have hR : 𝔏 R := lowerSaddleRisk_positive hcf _
  have hlow := hb.1
  have hε : ε ≤ 𝔅*𝚔₂ := by
    apply (div_le_iff₀ (by positivity : 0 < 𝚔₂)).mp
    exact hx.le
  have hfrac : 𝔇*𝔅 ≤ q := by
    have hp : 0 ≤ q := hq.le
    have he : 𝔇*𝔅 = 𝔇*q /(𝔇+1) := 𝖢₃
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < 𝔇+1)).mpr
    nlinarith only [hp]
  have hp1 := mul_le_mul_of_nonneg_left hε $ sq_nonneg DV
  have hp2 := mul_le_mul_of_nonneg_right hfrac $ sq_nonneg S
  have hpen : 𝔇*ε ≤ q*𝚔₂ := by nlinarith only [hp1,hp2]
  have hmain := mul_le_mul_of_nonneg_left ((sq_le_sq₀  𝖠₃  hR.le).mpr hlow) hα.le
  rw [mul_pow, Real.sq_sqrt hq.le ]
  dsimp [q] at hpen ⊢
  nlinarith only [hpen,hmain]
