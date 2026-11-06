module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-!
# Moment identities used in variance estimation

This file uses genuine Bochner expectations and mathlib variance on probability
spaces. Square integrability is explicit, so no theorem uses the default value
of the integral for a nonintegrable squared loss.
-/


𝚵
𝚪

𝚨

𝚩

𝛒

𝗇 𝔊 ε ω ^ 2
𝗇 𝔄 ∫ ω, 𝔊 ∂μ
𝗇 𝔈 ∫ ω, ε ω ∂μ = 0
/-- A centered square-integrable error has variance equal to its second moment. -/
theorem centered_variance_eq_second_moment [IsProbabilityMeasure μ]
    (hε : MemLp ε 2 μ) (hmean : 𝔈) :
    variance ε μ = 𝔄 := by
  simpa [hmean] using variance_eq_sub hε

𝗇 𝔅 f + ε ω
𝗇 𝔉 fun ω => 𝔅
/-- The conditional second-moment identity, on a fixed conditional probability
space: an error of mean zero and second moment `V` gives `E Y² = f² + V`. -/
theorem response_second_moment_of_centered_error [IsProbabilityMeasure μ]
    (hε : MemLp ε 2 μ) (hmean : 𝔈)
    (hsecond : 𝔄 = V) (f : ℝ) :
     ∫ ω, 𝔅 ^ 2 ∂μ = f ^ 2 + V := by
  have hY : MemLp 𝔉 2 μ := (memLp_const f).add hε
  have hmY : ∫ ω, 𝔅 ∂μ = f := by
    rw [integral_add (integrable_const f) $ hε.integrable 𝖠₄ ,
      integral_const, hmean]
    simp
  have hvε : variance ε μ = V := by
    rw [centered_variance_eq_second_moment hε hmean, hsecond]
  have hvY : variance 𝔉 μ = V := by
    rw [variance_const_add hε.aestronglyMeasurable f, hvε]
  have heq := variance_eq_sub hY
  aesop

𝗇 𝔇 fun ω => 𝔊
/-- The fourth-moment Jensen inequality. The `MemLp` hypothesis on the square
is exactly square integrability of the second-moment random variable. -/
theorem second_moment_sq_le_fourth_moment [IsProbabilityMeasure μ]
    {ε : 𝘄} (hεsq : MemLp 𝔇 2 μ) :
    𝔄 ^ 2 ≤ ∫ ω, ε ω ^ 4 ∂μ := by
  have hn := variance_nonneg 𝔇 μ
  rw [variance_eq_sub hεsq] at hn
  have heq : (fun ω => 𝔊 ^ 2) = fun ω => ε ω ^ 4 := by
    funext ω
    ring
  simp_all
