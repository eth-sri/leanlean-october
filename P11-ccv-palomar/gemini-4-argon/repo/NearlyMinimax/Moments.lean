module

public import Mathlib

@[expose] public section

/-!
# Moment identities used in variance estimation

This file uses genuine Bochner expectations and mathlib variance on probability
spaces. Square integrability is explicit, so no theorem uses the default value
of the integral for a nonintegrable squared loss.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace NearlyMinimax

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The conditional second-moment identity, on a fixed conditional probability
space: an error of mean zero and second moment `V` gives `E Y² = f² + V`. -/
theorem response_second_moment_of_centered_error [IsProbabilityMeasure μ]
    {ε : Ω → ℝ} (hε : MemLp ε 2 μ) (hmean : ∫ ω, ε ω ∂μ = 0)
    {V : ℝ} (hsecond : ∫ ω, ε ω ^ 2 ∂μ = V) (f : ℝ) :
    (∫ ω, (f + ε ω) ^ 2 ∂μ) = f ^ 2 + V := by
  have hmY : (∫ ω, f + ε ω ∂μ) = f := by
    rw [integral_add (integrable_const f) (hε.integrable (by norm_num)),
      integral_const, hmean]
    simp
  have hvε : variance ε μ = V := by
    have h_centered_variance_eq_second_moment : variance ε μ = ∫ ω, ε ω ^ 2 ∂μ := by
      simpa [hmean] using variance_eq_sub hε
    rw [h_centered_variance_eq_second_moment, hsecond]
  have hvY : variance (fun ω => f + ε ω) μ = V := by
    rw [variance_const_add hε.aestronglyMeasurable f, hvε]
  have heq := variance_eq_sub ((memLp_const f).add hε)
  change variance (fun ω => f + ε ω) μ =
    (∫ ω, (f + ε ω) ^ 2 ∂μ) - (∫ ω, f + ε ω ∂μ) ^ 2 at heq
  rw [hvY, hmY] at heq
  linarith

/-- The fourth-moment Jensen inequality. The `MemLp` hypothesis on the square
is exactly square integrability of the second-moment random variable. -/
theorem second_moment_sq_le_fourth_moment [IsProbabilityMeasure μ]
    {ε : Ω → ℝ} (hεsq : MemLp (fun ω => ε ω ^ 2) 2 μ) :
    (∫ ω, ε ω ^ 2 ∂μ) ^ 2 ≤ ∫ ω, ε ω ^ 4 ∂μ := by
  have hn := variance_nonneg (fun ω => ε ω ^ 2) μ
  rw [variance_eq_sub hεsq] at hn
  have heq : (fun ω => (ε ω ^ 2) ^ 2) = (fun ω => ε ω ^ 4) := by
    funext ω
    ring
  change 0 ≤ (∫ ω, (ε ω ^ 2) ^ 2 ∂μ) - (∫ ω, ε ω ^ 2 ∂μ) ^ 2 at hn
  rw [heq] at hn
  linarith

end NearlyMinimax
