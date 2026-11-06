module
public import DensityWindowBudgets
public import AdjacentAdditiveEnergy
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment
structure AdjacentWindow (σ a p α : ℝ) : Prop where
  sigma_low : 9/13 ≤ σ
  sigma_high : σ ≤ 3/4
  a_low : 7/10 ≤ a
  a_high : a ≤ 4/5
  p_low : 5/9 ≤ p
  alpha_low : a ≤ α
  alpha_high : α ≤ 1
  p_identity : p=3*a*(1-σ)
  mean_identity : 1+α*(1-2*σ)=p
  amplifier_lower : 0 ≤ p+α*(6*σ-5)
  cubic_lower : 4/5 ≤ p+a*(6*σ-4)
  amplifier_upper : p+α*(6*σ-4) ≤ 1
  cubic_balance : 2 ≤ 5*p/2+a*(12*σ-8)
  energy_first : 1+α*(6-8*σ) ≤ 2*p
  energy_resonant : 1+a*(9/2-7*σ) ≤ p
  energy_adjacent_third : 3 ≤ (5/2)*p+a*(14*σ-8)
  energy_adjacent_fourth : 9/4 ≤ (29/12)*p+a*(14*σ-9)
  typeII : 2-2*σ+1/50 ≤ p

theorem adjacent_amplifier_budgets {σ a p α T N : ℝ}
    (hw : AdjacentWindow σ a p α) (hT : 1 ≤ T) (hN : 0 < N)
    (hlo : T^a ≤ N) (hhi : N ≤ T^α) :
    N ≤ twoTermAmplifier T N σ p ∧ T^((4:ℝ)/5) ≤ twoTermAmplifier T N σ p ∧
      twoTermAmplifier T N σ p ≤ T ∧ T^((5:ℝ)/9) ≤ T^p ∧ (T/twoTermAmplifier T N σ p)^4 ≤ T^p := by
  pm_3943
  · have hl : T^(1-p/4) ≤ twoTermAmplifier T N σ p := by
      calc
        _ ≤ T^(p+a*(6*σ-4)) := Real.rpow_le_rpow_of_exponent_le hT (by linarith [hw.cubic_balance])
        _ = T^p*(T^a)^(6*σ-4) := by rw [hpow,← Real.rpow_add hTp]
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hlo he) (by positivity)
    have hlp : 0 < twoTermAmplifier T N σ p := by unfold twoTermAmplifier; positivity
    have hdiv : T/twoTermAmplifier T N σ p ≤ T/(T^(1-p/4)) :=
      div_le_div_of_nonneg_left hTp.le (by positivity) hl
    calc
      _ ≤ (T/(T^(1-p/4)))^4 := pow_le_pow_left₀ (div_nonneg hTp.le hlp.le) hdiv 4
      _ = T^(4*(1-(1-p/4))) := by
        rw [← Real.rpow_natCast (T/(T^(1-p/4))) 4,
          Real.div_rpow hTp.le (Real.rpow_nonneg hTp.le _),
          ← Real.rpow_mul hTp.le,← Real.rpow_sub hTp]
        congr 1
        ring
      _ = _ := by congr 1; ring

end Montgomery.RationalMoment
