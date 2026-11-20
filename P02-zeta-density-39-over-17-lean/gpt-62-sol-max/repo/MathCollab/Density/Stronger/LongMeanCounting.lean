module
public import MathCollab.Density.Stronger.LongMeanScale
public import MathCollab.Density.Stronger.SeparatedCriticalSampling
public import MathCollab.Density.Stronger.LongBlockDetection
public import MathCollab.Density.Stronger.ShortFixedFamily

@[expose] public section
open Filter MeasureTheory
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- The long-scale lower bound gives this finite counting inequality before
any moment estimate is used. -/
theorem long_mean_twelfth_count {A : ℕ} {U : Finset ℝ} {C X Y T σ : ℝ}
    (hX : 0 ≤ X) (hY : 0 < Y)
    (hmean : ∀ u ∈ U, Y^((σ-1/2)/2) ≤
      48*C*Real.sqrt X*Real.log T*weightedCriticalMean A u) :
    (U.card : ℝ)*Y^(6*σ-3) ≤
      (48*C)^12*X^6*(Real.log T)^12 * ∑ u ∈ U, (weightedCriticalMean A u)^12 := by
  have hscale : (Y^((σ-1/2)/2))^12 = Y^(6*σ-3) := by
    rw [← Real.rpow_mul_natCast hY.le]
    congr 1
    norm_num
    ring
  have hsqrt : (Real.sqrt X)^12 = X^6 := by
    calc
      _ = ((Real.sqrt X)^2)^6 := by ring
      _ = _ := by rw [Real.sq_sqrt hX]
  have hh (u : ℝ) (hu : u ∈ U) :
      Y^(6*σ-3) ≤ (48*C)^12*X^6*(Real.log T)^12*(weightedCriticalMean A u)^12 := by
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg hY.le ((σ-1/2)/2)) (hmean u hu) 12
    rw [hscale] at hp
    simpa only [mul_pow, hsqrt] using hp
  have hh' := Finset.sum_le_sum hh
  simpa only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] using hh'

theorem long_mean_count_le_physical_moment {U : Finset ℝ} {C X Y T σ : ℝ}
    (hT : 1 ≤ T) (hX : 0 ≤ X) (hY : 0 < Y)
    (hU : oneSeparated U) (hslab : ∀ u ∈ U, u ∈ Set.Icc T (2*T))
    (hmean : ∀ u ∈ U, Y^((σ-1/2)/2) ≤
      48*C*Real.sqrt X*Real.log T*weightedCriticalMean 128 u) :
    (U.card : ℝ)*Y^(6*σ-3) ≤ (48*C)^12*X^6*(Real.log T)^12 *
      (Real.pi^11 * separationMass * (∫ t in Set.Icc 0 (3*T), zetaMomentCriticalNorm t^12) +
        (2*(12:ℝ)^12*Real.pi^12)*T^(-113 : ℝ)) := by
  apply (long_mean_twelfth_count hX hY hmean).trans
  exact mul_le_mul_of_nonneg_left (separated_weightedCriticalMean_twelfth_le hT hU hslab)
    (by positivity)

end MathCollab.Density.Stronger
