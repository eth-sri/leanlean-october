module

public import NearlyMinimax.CompleteSaddleEnergy
public import NearlyMinimax.HighWindowFactorialEnergy
public import NearlyMinimax.HighUnionRawFisher
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Exact finite-window accounting for the concrete saddle envelope. The
full source series has the factor 3^d k^d and the proved actual factorial
energy budget. -/
open MeasureTheory Filter
𝚪
𝚨
𝚩

𝗇 𝔄 lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω n
𝗇 𝔍 completeSaddleGeometryEnvelope C Q Cfr cf Cω n
𝗇 𝔅 fun _j => 𝔍
𝗇 𝔇 completeSaddleMu C Cω n
section

variable (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C)

𝗇 𝔈 (𝚐 : ℕ)*𝔄^d
𝗇 𝔉 highSourceSpatialSeries d 𝔄 n C.densityLower Q.c 𝔅
𝗇 𝔊 completeSaddleScoreFactor C Q*𝔇
theorem completeSaddleSpatialSeries_eq (Cfr cf Cω : ℝ) (n : ℕ)
    [NeZero 𝔄] :
    𝔉 =
    𝔈 *
       ∑ r ∈ Finset.range 𝗉, poissonCountWeight
        𝔊 r *
        ∫ u, 𝔍 r u ∂𝗾₂ := by
  let k := 𝔄
  have hmu : 𝔇 = n/𝗋 := by
    dsimp only [completeSaddleMu,lowerSaddleMu,lowerSaddleH]
    aesop
  have hparameter : n*highFixedScoreDenominator C.densityLower Q.c*𝗄 =
      𝔊 :=
    high_design_factorial_parameter (highFixedScoreDenominator C.densityLower Q.c)
      𝔇 hmu
  change highSourceSpatialSeries d k n C.densityLower Q.c _ = _
  simp only [highSourceSpatialSeries,hparameter,Finset.sum_const,Finset.card_univ,
    highWindowLabels_card]
  simp only [poissonCountWeight,fullSpatialPatchDesign]
  ring

theorem eventually_completeSaddleSpatialSeries_le [NeZero d]
    (hs : 𝘎) (hd : 𝘊 < 𝙊)
    (hcf : 𝙻₁) Cfr Cω :
    ∀ᶠ n : ℕ in atTop,
      ∀ hk0 : NeZero 𝔄,
      𝔉 ≤
      𝔈 *
          completeSaddleEnergyBudget C Q Cfr cf Cω n := by
  filter_upwards [eventually_completeSaddleGeometry_factorial C Q hs hd hcf Cfr Cω] with n hn
  intro hk0
  letI := hk0
  rw [completeSaddleSpatialSeries_eq]
  bound
