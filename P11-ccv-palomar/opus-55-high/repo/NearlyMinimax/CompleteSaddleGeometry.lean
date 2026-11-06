module

public import NearlyMinimax.HighSourceAllGeometry
public import NearlyMinimax.HighGeometryEnvelopeMonotone
public import NearlyMinimax.OrdinaryFineAliasSaddleEnvelope
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The concrete geometry-only envelope at the actual rounded source
saddle. Its count profile uses the true normalized activation budget. -/
𝚫
𝚨
𝚩
𝚽
𝚬

 set_option hygiene false
𝗇 𝔅 𝙲
𝗇 𝔈 𝘁₂+1
𝗃 𝔊 ἀ C.smoothness d m theta Cω
def completeSaddleGeometryEnvelope (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cfr cf Cω : ℝ) (n : ℕ) :
    𝗖 :=
  let q := lowerSaddleResponseOrder C.smoothness d
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  let c0 := 𝔈
  let M := lowerSaddleM m n
  let D := lowerSaddleD d m n
  let N := 𝔊 lowerSaddleN 𝔅 n
  let mu := 𝙰₂ Cω n
  let ell := 𝔊 lowerAliasCutoff c0 𝔅 n
  let eta := 𝔊 lowerSaddleEta cf n
  let Rbound := ordinaryFineAliasSaddleTargetBound C.smoothness d C.densityLower C.densityUpper
  let Chi := 𝙪₂
  let Bl := completeSourceSaddleActivity C q Cfr (spatialInterpolationLambda d) Cω n
  𝙱₂ Bl

 set_option hygiene false
𝗇 𝔇 completeSaddleGeometryEnvelope C Q Cfr cf Cω n r
theorem completeSaddleGeometryEnvelope_nonneg (C : ModelConstants d)
    Q Cfr cf Cω n r U :
    0 ≤ 𝔇 U :=
  completeSourceGeometryEnvelope_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r U

 set_option hygiene false
𝗃 𝔉 ἀ C.smoothness d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω
𝗇 𝔄 𝔉 lowerAliasCutoff 𝔈 𝙲 n
theorem completeSaddleGeometryEnvelope_integrable [NeZero d] (C : ModelConstants d)
    Q (hd : 𝘚) Cfr cf Cω (n r : ℕ)
    (hell : 1 ≤ 𝔄)
    (hellN : 𝔄 ≤
      𝔉 lowerSaddleN 𝔅 n) :
    Integrable 𝔇 𝗾₂ :=
  by
    apply completeSourceGeometryEnvelope_integrable hd
    all_goals assumption
