module

public import NearlyMinimax.CompleteSourceSaddleParameters
public import NearlyMinimax.LowerPenaltyReduction
public import NearlyMinimax.PaperGoals
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Numerical ending of the true complete-source cost construction. The
hypotheses are actual activity and primitive energy caps, never a desired
statistical rate or minimax conclusion. -/
𝚷
𝚶
𝚨
𝚩
𝚭

 set_option hygiene false
𝗇 𝔄 𝙊
𝗇 𝔅 𝙽₁
𝗇 𝔇 𝙲
𝗇 𝔈 𝔄+4
theorem completeSourceSaddle_penalized_numeric_envelope [NeZero d]
    (C : ModelConstants d) (hs : 𝘎) (hd : 𝘊 < 𝔄)

    (hcf : 𝙻₁) (hCB : 0 ≤ CB) (hC5 : 0 ≤ C5) (hC6 : 0 ≤ C6)
    (hC7 : 0 ≤ C7) (hch : 0 ≤ ch) (hctr : 0 < ctr) (hcm : 0 < cm)
    (hshift : 1+Real.log 𝔅+
      (𝔄^2-16*C.smoothness)/(𝔄*𝔈)*highCompleteSourceSaddleTheta C+
      𝖩₁*𝘁₂/𝔈 < Cω) :
    ∃ c , 𝘝 ∧ ∀ᶠ n : ℕ in atTop,
      let m := highCompleteSourceSaddleCoefficient C
      let theta := highCompleteSourceSaddleTheta C
      let tauM := 𝔇
      let k := 𝙼₁
      let eta := 𝖿
      let B := lowerSaddleActivity C.smoothness d m theta Cω tauM n
      ∀ Bl E , 1 ≤ B → 0 ≤ Bl → 𝘃₂ → Bl ≤ CB*B →
      𝙲₂ →
      (c*paperRiskScale C n)^2 ≤ ctr*𝗸/(𝘄₂+𝗋*E)-
        𝙰^2*highCompleteSourceSaddleTail C Cω cm n := by
  have hab := C.densityLower_lt_one.trans C.one_lt_densityUpper
  let CG := 𝔅
  have hCG : 0 < CG := lt_of_lt_of_le zero_lt_one $ rawCostConstant_ge_one ..
  obtain ⟨c,hc,hpen⟩ := eventually_actual_lowerSaddle_penalized_rate_square
    hs hd C.densityLower_pos hab hcf hCG hctr hcm (highHistoryMassMomentConstant_pos d C.densityLower C.densityUpper hab) Cω
  have hcost := eventually_actual_lowerSaddle_raw_cost hs hd C.densityLower_pos hab
    hcf.le hCB hC5 hC6 hC7 hch hshift
  refine ⟨c,hc,?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hpen,
    tendsto_natCast_atTop_atTop.eventually hcost,eventually_ge_atTop 2] with n hn hcst hn2
  dsimp at hn hcst ⊢
  intro Bl E hB hBl hE hBlcap hEcap
  have hvolume := completeSourceSaddle_inverse_volume C Cω n
  have hcost' : 𝘄₂+
      (lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
        (highCompleteSourceSaddleTheta C) Cω n : ℝ)^d*E ≤
      3*CG* lowerSaddleActivity C.smoothness d (highCompleteSourceSaddleCoefficient C)
        (highCompleteSourceSaddleTheta C) Cω
        𝔇 n ^2 := by
    rw [hvolume]
    exact hcst Bl E hB hBl hBlcap hEcap
  have hmain := lowerSaddle_cost_risk_reduction (cf := cf)
    𝔇  𝖠₃  hCG hctr.le hcost'
  rw [← completeSourceSaddle_eta_eq C Cω cf n] at hmain
  rw [ paperRiskScale_eq_rateScale C hn2 ]
  apply hn.trans
  exact sub_le_sub_right hmain _
