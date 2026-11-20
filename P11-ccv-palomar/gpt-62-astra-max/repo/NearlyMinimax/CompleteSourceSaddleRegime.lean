module

public import NearlyMinimax.CompleteSourceSaddleParameters
public import NearlyMinimax.SourceSaddleHigherSelection

@[expose] public section

/-! Fixed regularity and physical higher-row guards at the actual natural
sample sequence. These are consequences of the rounded saddle definitions. -/
noncomputable section
open Filter
namespace NearlyMinimax

 variable {d : ℕ} {C : ModelConstants d} (hs : 1 < C.smoothness) (hd : 4*C.smoothness < (d : ℝ))
include hd hs

theorem completeSourceSaddle_fixed_regime_window
    {cf : ℝ} (hcf : 0 < cf) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ Cω eta0 M0, 0 < eta0 →
      ∀ᶠ n : ℕ in atTop,
        LowerSaddleReg K eta0 C.smoothness d (highCompleteSourceSaddleCoefficient C)
          (highCompleteSourceSaddleTheta C) Cω cf M0
          (shrunkDensityExponent C.densityLower C.densityUpper) n := by
  obtain ⟨K,hK,h⟩ := actual_lowerSaddle_fixed_regime_window hs hd C.densityLower_pos
    (C.densityLower_lt_one.trans C.one_lt_densityUpper) hcf
  refine ⟨K,hK,fun Cω eta0 M0 heta0 => ?_⟩
  solve_by_elim [tendsto_natCast_atTop_atTop.eventually]

end NearlyMinimax
