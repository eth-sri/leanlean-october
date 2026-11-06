module
import Mathlib
public import GuthMaynard.Improvement.ShortDensityHeight

@[expose] public section


namespace GuthMaynard.Improvement





section
variable {σ H N : ℝ}
    (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) (hH : 1 ≤ H)
include σ H N hσ hσ' hH




end


/- Threshold algebra retains the original H even when the time is padded. -/
theorem upper_window_padded_denominator {H N : ℝ} (hH : 0 < H) (hN : 0 < N)
    (S σ δ : ℝ) :
    N^(18/7:ℝ)*S^(6/7:ℝ)/(N^σ*H^(-2*δ))^4 =
      (N^(18/7-4*σ)*S^(6/7:ℝ))*H^(8*δ) := by
  have hV := (short_density_height_eq hH hN σ δ).1
  have hn4 : N^(18/7-4*σ) = N^(18/7:ℝ)/(N^σ)^4 := by
    rw [Real.rpow_sub hN,show 4*σ = σ*4 by ring,
      Real.rpow_mul hN.le σ 4,Real.rpow_ofNat]
  have hh8 : H^(8*δ) = (H^δ)^8 := by
    rw [show 8*δ = δ*8 by ring,Real.rpow_mul hH.le δ 8,Real.rpow_ofNat]
  grind


