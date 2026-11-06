module
public import RationalDyadicShortRange
public import RationalDifferenceEnergy

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem short_length_le_twice_time {K : ℕ} (hK : 1 ≤ K)
    {T t₀ M : ℝ} (hT : 1 < T) (W : Finset ℝ)
    (hMR : M^K ≤ W.card)
    (hW : ∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T))
    (hsep : ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) : M ≤ 2*T := by
  by_cases hm : M ≤ 1
  · linarith
  · have hpow : M ≤ M^K := by
      simpa only [pow_one] using pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hm)) hK
    have hp := separated_interval_card (by linarith : 0 ≤ T) W hW hsep
    linarith

theorem logarithmic_height_loss {T δ : ℝ} (hT : 1 ≤ T) (hδ : 0 < δ)
    (N : ℕ) (hN : (N : ℝ) ≤ 4*T) :
    1+Real.log N ≤ (1+4^δ/δ)*T^δ := by
  have hTp : 0 < T := by linarith
  have hpow : 1 ≤ T^δ := Real.one_le_rpow hT hδ.le
  have hlog : Real.log N ≤ (4^δ*T^δ)/δ := by
    calc
      _ ≤ (N : ℝ)^δ/δ := Real.log_natCast_le_rpow_div N hδ
      _ ≤ (4*T)^δ/δ := by
        apply div_le_div_of_nonneg_right _ hδ.le
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) hN hδ.le
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hTp.le]
  calc
    _ ≤ T^δ+(4^δ*T^δ)/δ := add_le_add hpow hlog
    _ = _ := by ring

end Montgomery.RationalMoment
