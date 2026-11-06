module

public import NearlyMinimax.CompleteSourceInvariantMass
public import NearlyMinimax.HighUnionTiltedTail
public import NearlyMinimax.HighMassTailScale
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Genuine exceptional-mass tails of the complete singleton/pair/higher
row prior, specialized to the actual rounded lower saddle. The deterministic
envelope is fixed before the extension domain and all source times. -/
𝛅
𝚶
𝚨
𝚩
𝛆
𝚬

section Pointwise
variable {d k D M q : ℕ} [NeZero d] [NeZero k] [LinearOrder 𝙯]
    (C : ModelConstants d) (hD : 𝗕) (hq : 𝗘)
    (hM : highCenterResolutionThreshold C ≤ 𝖧)
    (Cfr lam ell N mu : ℝ) (hCfr : 𝗹) (hell : 𝚁₁) (hellN : 𝘈₂)
include hD hq hM hCfr hell hellN

𝗇 𝔄 𝖻 lam ell N mu
𝗇 𝔅 𝚐
𝗇 𝔇 8*highHistoryMassParameter d k C.densityLower C.densityUpper
𝗃 𝔉 ἀ 𝔄 $ highCenterMix C
/-- Every time of the actual complete-row source has the genuine tilted
exceptional bound. All mass-law and local cancellation premises are
discharged by the true complete packet construction. -/
theorem completeSourceMass_prior_tilted_tail (hk : 𝚂) T (hT : 𝚞)
    (hsmall : T*(highRowTotalMass (𝔄).rowMass /
      highCenterMix C)/historyReferenceRho 𝔅 ≤ 1/(2+8* (𝔅:ℕ) ^2))
    (n : ℕ) epsilon
    (hepsilon : 𝔇*n ≤ epsilon)
    t (ht : t ∈ 𝗺) :
    (massPowerTilt
      (historyMarkedPrior 𝖫 𝔅 t
        𝔉 highUnionLaw
        𝔉 highUnionActivation)
      (highUnionSourceMass C 𝔄) n).real
      {h | epsilon < |highUnionSourceMass C 𝔄 h-1|} ≤
      2*Real.exp (-epsilon^2/𝔇) := by
  have G := 𝖠 ell N mu hCfr hell hellN
  rw [massPowerTilt_abs_event_eq_of_massLaw _ _ _ (highUnionSourceMass_measurable C _ G) n
    (completeSourceMass_prior_law C hD hq hM Cfr lam ell N mu hCfr hell hellN T hT hsmall t ht) epsilon]
  exact highUnionSourceMass_reference_tilted_tail C _ G hk n epsilon hepsilon

end Pointwise

𝗇 𝔈 𝘁₂
/-- The fixed canonical source coefficient; it depends only on model constants. -/
def highCompleteSourceSaddleCoefficient (C : ModelConstants d) : ℝ :=
  lowerSaddleCoefficient C.smoothness d 𝔈

def highCompleteSourceSaddleTheta (C : ModelConstants d) : ℝ :=
  lowerSaddleTheta C.smoothness d 𝔈

/-- The actual geometric envelope for the complete-row tilted bad mass. -/
def highCompleteSourceSaddleTail (C : ModelConstants d) (Cω cm : ℝ) (n : ℕ) : ℝ :=
  lowerSaddleExceptionalTail d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω
    (cm^2/(8*highHistoryMassMomentConstant d C.densityLower C.densityUpper)) n
