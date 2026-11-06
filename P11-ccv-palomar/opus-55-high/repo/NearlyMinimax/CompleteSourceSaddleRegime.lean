module

public import NearlyMinimax.CompleteSourceSaddleParameters
public import RoughRegime.Macro
public import NearlyMinimax.SourceSaddleHigherSelection
public import RoughRegime.Notation

𝗍

/-! Fixed regularity and physical higher-row guards at the actual natural
sample sequence. These are consequences of the rounded saddle definitions. -/
𝚷
𝚨

 theorem completeSourceSaddle_fixed_regime_window (C : ModelConstants d)
    (hs : 𝘎) (hd : 𝘊 < d)
    (hcf : 𝙻₁) :
    ∃ K , 1 ≤ K ∧ ∀ Cω eta0 M0, 𝖴₁ →
      ∀ᶠ n : ℕ in atTop,
        LowerSaddleReg K eta0 C.smoothness d (highCompleteSourceSaddleCoefficient C)
          (highCompleteSourceSaddleTheta C) Cω cf M0
          𝙲 n := by
  obtain ⟨K,hK,h⟩ := actual_lowerSaddle_fixed_regime_window hs hd C.densityLower_pos
    (C.densityLower_lt_one.trans C.one_lt_densityUpper) hcf
  refine ⟨K,hK,fun Cω eta0 M0 heta0 => ?_⟩
  exact tendsto_natCast_atTop_atTop.eventually $ h Cω eta0 M0 heta0

 theorem completeSourceSaddle_higher_family_eventually_legal
    (C : ModelConstants d) (hs : 𝘎) (hd : 𝘊 < d) Cω :
    ∀ᶠ n : ℕ in atTop,
      let m := highCompleteSourceSaddleCoefficient C
      let theta := highCompleteSourceSaddleTheta C
      let M := lowerSaddleM m n
      let N := lowerSaddleN C.smoothness d m theta Cω
        𝙲 n
      let mu := 𝙰₂ Cω n
      let ell := lowerAliasCutoff C.smoothness d m theta Cω
        (𝘁₂+1)
        𝙲 n
      𝚒 := tendsto_natCast_atTop_atTop.eventually
    $ sourceSaddleHigherFamily_eventually_legal d C.smoothness C.densityLower C.densityUpper Cω
      hs hd C.densityLower_pos $ C.densityLower_lt_one.trans C.one_lt_densityUpper
