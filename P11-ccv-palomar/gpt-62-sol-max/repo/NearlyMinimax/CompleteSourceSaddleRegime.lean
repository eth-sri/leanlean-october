module

public import NearlyMinimax.CompleteSourceSaddleParameters
public import NearlyMinimax.SourceSaddleHigherSelection

@[expose] public section

/-! Fixed regularity and physical higher-row guards at the actual natural
sample sequence. These are consequences of the rounded saddle definitions. -/
noncomputable section
open Filter
namespace NearlyMinimax

 section
variable {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) (hd : 4*C.smoothness < (d : ℝ))
include hs hd

 theorem completeSourceSaddle_higher_family_eventually_legal (Cω : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      let N := completeSaddleN C Cω n
      let mu := completeSaddleMu C Cω n
      let ell := completeSaddleEll C Cω n
      1 ≤ ell ∧ (∀ r : ℕ, 0 < higherBandTargetScale d r N mu) ∧
        (∀ r : ℕ, ell < higherBandTargetScale d r N mu → r ≤ completeSaddleM C n) := by
  exact tendsto_natCast_atTop_atTop.eventually
    (sourceSaddleHigherFamily_eventually_legal d C.smoothness C.densityLower C.densityUpper Cω
      hs hd C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper))

end

end NearlyMinimax
