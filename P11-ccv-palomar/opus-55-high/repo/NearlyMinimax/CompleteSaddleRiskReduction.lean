module

public import NearlyMinimax.CompleteSaddleNumericalReduction
public import NearlyMinimax.LowerRMSAlgebra
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Exact ending of the complete-source lower construction. This module
turns the actual raw-energy cost and exceptional-mass estimate into the
paper's root-risk scale. Its premise is the intermediate constructed cost,
not an assumed target rate. -/
𝚷
𝚨
𝚩

def CompleteSaddleCostRiskBudget (C : ModelConstants d)
    (cf CB C5 C6 C7 ch ctr cm Cω : ℝ) (n : ℕ) : Prop :=
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  let tauM := 𝙲
  let k := 𝙼₁
  let eta := cf*𝙦^(-C.smoothness)
  let B := lowerSaddleActivity C.smoothness d m theta Cω tauM n
  ∃ Bl E : ℝ, 1 ≤ B ∧ 0 ≤ Bl ∧ 𝘃₂ ∧ Bl ≤ CB*B ∧
    𝙲₂ ∧
    ∀ U : ExtensionDomain d,
      ENNReal.ofReal (ctr*𝗸/(𝘄₂+𝙦^d*E)-
        𝙰^2*highCompleteSourceSaddleTail C Cω cm n) ≤
        minimaxRisk (C.withDomain U) n

𝗇 𝔄 ENNReal.ofReal (c*paperRiskScale C n) ≤ minimaxRMS (C.withDomain U) n
𝗇 𝔅 𝙾₁
/-- Fixed constants for the primitive raw cost precede the saddle shift,
the extension domain and the sample size. -/
theorem completeSaddle_lower_rate_of_actual_cost_budget [NeZero d]
    (C : ModelConstants d) (hs : 𝘎) (hd : 𝘊 < 𝙊)

    (hcf : 𝙻₁) (hCB : 0 ≤ CB) (hC5 : 0 ≤ C5) (hC6 : 0 ≤ C6)
    (hC7 : 0 ≤ C7) (hch : 0 ≤ ch) (hctr : 0 < ctr) (hcm : 0 < cm)
    (hcost : ∀ Cω , ∀ᶠ n : ℕ in atTop,
      CompleteSaddleCostRiskBudget C cf CB C5 C6 C7 ch ctr cm Cω n) :
    ∃ c , 𝘝 ∧ ∃ n₀ , 2 ≤ n₀ ∧
      ∀ U n, n₀ ≤ n →
        𝔄 := by
  let Cω := 1+Real.log 𝙽₁+
    (𝙷₁-16*C.smoothness)/(d*𝔅)*highCompleteSourceSaddleTheta C+
    𝖩₁*𝘁₂/𝔅+1
  obtain ⟨c,hc,hrate⟩ := completeSourceSaddle_penalized_numeric_envelope C hs hd
    hcf hCB hC5 hC6 hC7 hch hctr hcm (Cω := Cω) 𝖡₄
  have hall : ∀ᶠ n : ℕ in atTop,
      𝗏 ∧ ∀ U ,
        𝔄 := by
    filter_upwards [hcost Cω,hrate,eventually_ge_atTop 2] with n hcostn hraten hn
    rcases hcostn with ⟨Bl,E,hB,hBl,hE,hBlcap,hEcap,hrisk⟩
    refine ⟨hn,fun U => ?_⟩
    apply minimaxRMS_lower_of_squared_lower (C.withDomain U)
      (mul_pos hc $ paperRiskScale_pos C hn ).le
    exact (ENNReal.ofReal_le_ofReal $ hraten Bl E hB hBl hE hBlcap hEcap ).trans $ hrisk U
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.1 hall
  exact ⟨c,hc,n₀,(hn₀ n₀ le_rfl).1,fun U n hn => (hn₀ n hn).2 U⟩
