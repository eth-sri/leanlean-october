module
public import DensityWindowBudgets
public import AdjacentAdditiveEnergy

public import DensityDetectorWindows

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

theorem adjacent_amplifier_budgets {σ a p α T N : ℝ}
    (hw : AdjacentWindow σ a p α) (hT : 1 ≤ T) (hN : 0 < N)
    (hlo : T^a ≤ N) (hhi : N ≤ T^α) :
    N ≤ twoTermAmplifier T N σ p ∧ T^((4:ℝ)/5) ≤ twoTermAmplifier T N σ p ∧
      twoTermAmplifier T N σ p ≤ T ∧ T^((5:ℝ)/9) ≤ T^p ∧ (T/twoTermAmplifier T N σ p)^4 ≤ T^p := by
  have hTp : 0 < T := by linarith
  have he : 0 ≤ 6*σ-4 := by linarith [hw.sigma_low]
  have hnexp : 0 ≤ 5-6*σ := by linarith [hw.sigma_high]
  have ha : 0 ≤ a := by linarith [hw.a_low]
  have hp : 0 ≤ p := by linarith [hw.p_low]
  have hN1 : 1 ≤ N := (Real.one_le_rpow hT ha).trans hlo
  have hpow (q : ℝ) : (T^a)^q = T^(a*q) := (Real.rpow_mul hTp.le a q).symm
  have hpow' (q : ℝ) : (T^α)^q = T^(α*q) := (Real.rpow_mul hTp.le α q).symm
  have hlower : N^(5-6*σ) ≤ T^p := by
    calc
      _ ≤ (T^α)^(5-6*σ) := Real.rpow_le_rpow hN.le hhi hnexp
      _ = T^(α*(5-6*σ)) := hpow' _
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by linarith [hw.amplifier_lower])
  refine ⟨?_,?_,?_,Real.rpow_le_rpow_of_exponent_le hT hw.p_low,?_⟩
  · calc
      N = N^(5-6*σ)*N^(6*σ-4) := by rw [← Real.rpow_add hN]; convert (Real.rpow_one N).symm using 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hlower (Real.rpow_nonneg hN.le _)
  · calc
      _ ≤ T^(p+a*(6*σ-4)) := Real.rpow_le_rpow_of_exponent_le hT hw.cubic_lower
      _ = T^p*(T^a)^(6*σ-4) := by rw [hpow,← Real.rpow_add hTp]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hlo he) (by positivity)
  · calc
      _ ≤ T^p*(T^α)^(6*σ-4) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN.le hhi he) (by positivity)
      _ = T^(p+α*(6*σ-4)) := by rw [hpow',← Real.rpow_add hTp]
      _ ≤ T^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hT hw.amplifier_upper
      _ = T := Real.rpow_one T
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
