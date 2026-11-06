module

public import NearlyMinimax.CompleteSourceSaddleRegime
public import NearlyMinimax.LowerSaddleDegreeBounds
public import NearlyMinimax.FineFieldScaleBudget
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Every scalar guard used in the complete-source factorial energy bound
is a conclusion of the actual rounded saddle. Constants precede its shift
and sample size; no energy, regularity or desired-rate guard is assumed. -/
open Filter Set
𝚨
𝚩
𝚭

abbrev completeSaddleM (C : ModelConstants d) (x : ℝ) :=
  lowerSaddleM (highCompleteSourceSaddleCoefficient C) x
abbrev completeSaddleD (C : ModelConstants d) (x : ℝ) :=
  lowerSaddleD d (highCompleteSourceSaddleCoefficient C) x
𝗇 𝔉 𝙲
𝗃 𝔊 ἀ C.smoothness d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω
abbrev completeSaddleN (C : ModelConstants d) (Cω x : ℝ) :=
  𝔊 lowerSaddleN 𝔉 x
abbrev completeSaddleMu (C : ModelConstants d) (Cω x : ℝ) :=
  lowerSaddleMu d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω x
abbrev completeSaddleEta (C : ModelConstants d) (Cω cf x : ℝ) :=
  𝔊 lowerSaddleEta cf x
abbrev completeSaddleC0 (C : ModelConstants d) :=
  𝘁₂+1
abbrev completeSaddleEll (C : ModelConstants d) (Cω x : ℝ) :=
  𝔊 lowerAliasCutoff (completeSaddleC0 C)
    𝔉 x
𝗃 𝔒 ἀ C x
abbrev completeSaddleTau (C : ModelConstants d) (x : ℝ) :=
  𝔉 𝔒 completeSaddleM
𝗇 𝔄 (𝔒 completeSaddleM : ℝ)
abbrev completeSaddleAD (C : ModelConstants d) (x : ℝ) :=
  C.densityLower+1/𝔄
abbrev completeSaddleBD (C : ModelConstants d) (x : ℝ) :=
  C.densityUpper-1/𝔄

𝗇 𝔅 𝙊
𝗇 𝔇 completeSaddleN C Cω x
𝗇 𝔈 completeSaddleMu C Cω x
𝗇 𝔍 completeSaddleEll C Cω x
𝗇 𝔏 2-𝔅
structure CompleteSaddleEnergyGuards {d : ℕ} (C : ModelConstants d) (Cω cf x : ℝ) : Prop where
  resolution : highCenterResolutionThreshold C ≤ 𝔄
  N_one : 1 ≤ 𝔇
  mu_positive : 0 < 𝔈
  mu_one : 𝔈 ≤ 1
  mu_log : 𝔈*(1+Real.log 𝔇) ≤ 1
  response_taylor : completeSaddleEta C Cω cf x ^(4*lowerSaddleResponseOrder C.smoothness d)*
    𝔇^d ≤ 1
  tau_nonneg : 0 ≤ 𝔒 completeSaddleTau
  tau_le : 𝔒 completeSaddleTau ≤ completeSaddleC0 C
  degree_multiple : (𝔒 completeSaddleD : ℝ) ≤
    ((𝔅+8)/4+1)*𝔄
  ell_one : 1 ≤ 𝔍
  ell_lt_N : 𝔍 < 𝔇
  field_scale_square : Real.exp (2*𝔒 completeSaddleTau*𝔄)*
    𝔈^4*(𝔍^𝔏)^2 ≤
      𝔈^2*𝔇^(-𝔅)
  bd_nonneg : 0 ≤ 𝔒 completeSaddleBD
  ad_positive : 0 < 𝔒 completeSaddleAD
  density_interval : 𝔒 completeSaddleAD < 𝔒 completeSaddleBD

 𝗇 𝔎 completeSaddleEll C Cω n
𝗇 𝔐 tau+1
𝗇 𝔑 𝙋<1
theorem eventually_completeSaddleEnergyGuards [NeZero d]
    (C : ModelConstants d) (hs : 𝘎) (hd : 𝘊 < 𝔅)
    (hcf : 𝙻₁) (Cω : ℝ) :
    ∀ᶠ n : ℕ in atTop, CompleteSaddleEnergyGuards C Cω cf n := by
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  let tau := 𝘁₂
  have hab := C.densityLower_lt_one.trans C.one_lt_densityUpper
  have htau := densityIntervalExponent_pos C.densityLower_pos hab
  have hm := lowerSaddleCoefficient_pos hs hd htau
  have htheta := lowerSaddleTheta_pos hs hd htau
  obtain ⟨Ctau,_,hcontrol⟩ := exists_actual_lowerExponentControl C.densityLower_pos hab
  obtain ⟨K,_,hreg⟩ := completeSourceSaddle_fixed_regime_window C hs hd hcf
  have hhier := actual_lowerAlias_hierarchy (Cact := 1) (Cs := 1) hs hd
    C.densityLower_pos hab  𝖠₄   𝖠₄  Cω
  have hscale := eventually_lowerSaddle_fine_field_energy_scale hs hd hm htheta hcontrol Cω 𝔐
  have hparams := eventually_completeSourceSaddle_parameters C hs hd hcf
    (by norm_num : 𝔑) (by norm_num : 𝔑) Cω
  filter_upwards [hreg Cω 1 0 𝖠₄ ,tendsto_natCast_atTop_atTop.eventually hhier,
    tendsto_natCast_atTop_atTop.eventually hscale,
    tendsto_natCast_atTop_atTop.eventually hparams,
    tendsto_natCast_atTop_atTop.eventually
      $ 𝘂₂ $ eventually_ge_atTop 1 ]
    with n hregn hhiern hscalen hpn hMone
  rcases hregn with ⟨_,_,hN,hmu,hmu1,_,_,_,_,_,_,hqt⟩
  change LowerAliasHierarchy C.smoothness d m theta Cω 1 1 𝔐
    𝔉 n at hhiern
  rcases hhiern with ⟨hell,htaule,hmulog,_,_,_,_,_,_,_,_,_⟩
  obtain ⟨had,hadb⟩ := high_source_interval_numeric C (completeSaddleM C n) hpn.2.2.1
  have htn : 0 ≤ completeSaddleTau C n := by
    have hia : 0 < C.densityLower+(completeSaddleM C n : ℝ)⁻¹ := by simpa only [one_div] using had
    exact (densityIntervalExponent_pos hia $ by simpa only [one_div] using hadb ).le
  have hsquare : (𝔎^𝔏)^2 =
      𝔎^(4-2*𝔅) := by
    rw [← Real.rpow_mul_natCast $ by linarith only [hell] ]
    ring
  refine ⟨hpn.2.2.1,hN,hmu,hmu1.le,hmulog,?_,htn,htaule,
    lowerSaddleD_le_fixed_multiple (Nat.cast_nonneg _) hMone,hell.le,hpn.2.2.2.2.1,
    ?_,had.le.trans hadb.le,had,hadb⟩
  · simpa only [lowerSaddleResponseQuantity,Real.rpow_natCast] using hqt
  · rw [hsquare]
    exact hscalen
