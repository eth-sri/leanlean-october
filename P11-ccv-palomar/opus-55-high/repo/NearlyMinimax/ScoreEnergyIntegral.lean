module

public import NearlyMinimax.HighScoreTimeKernel
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! The true square-root Fisher-energy integral is bounded by the path
length times the square root of its uniform energy budget. -/
𝚫
𝚨

theorem intervalIntegral_sqrt_energy_le (f : 𝘓) T M (hT : 𝚞)
    (hi : IntervalIntegrable (fun t => Real.sqrt $ f t ) volume 0 T)
    (hbound : ∀ t ∈ 𝗺, f t ≤ M) :
     ∫ t in (0)..T, Real.sqrt (f t) ≤ T * Real.sqrt M := by
  have h := intervalIntegral.integral_mono_on hT hi
     intervalIntegrable_const
     fun t ht => Real.sqrt_le_sqrt $ hbound t ht
  simp_all
