module
public import DensityEnergyGM.SharpCountAlgebra
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

theorem eighth_gap_count_absorption {R S C : ℝ}
    (hS : 0 < S) (hSR : S ≤ R)
    (hbound : R^2 ≤ C*S^(1/8:ℝ)*R^(15/8:ℝ)) : R ≤ C^8*S := by
  have hR : 0 < R := hS.trans_le hSR
  have he : R^2=R^(1/8:ℝ)*R^(15/8:ℝ) := by
    rw [← Real.rpow_add hR]
    norm_num
  rw [he] at hbound
  have hh : R^(1/8:ℝ) ≤ C*S^(1/8:ℝ) :=
    (mul_le_mul_iff_left₀ (by positivity : 0 < R^(15/8:ℝ))).mp (by grind)
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ R^(1/8:ℝ)) hh 8
  pm_7043 hleft R hR.le
  pm_7043 hright S hS.le
  simpa only [hleft,mul_pow,hright] using hp

end Montgomery.RationalMoment
