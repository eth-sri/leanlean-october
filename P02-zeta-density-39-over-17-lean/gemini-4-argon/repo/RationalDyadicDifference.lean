module
public import RationalDyadicShortRange
public import RationalDifferenceEnergy

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment


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

