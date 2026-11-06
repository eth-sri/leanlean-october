module
public import LaterPairs.NativeTTY4
public import LaterPairs.TTY4TargetParameters
public import LaterPairs.PairActualDensity

@[expose] public section
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density

theorem tty4_prefix_density_exponent {σ : ℝ} :
    3*(31544/(107010*σ-33609))*(1-σ) =
      31544*(1-σ)/(35670*σ-11203) := by
  have hd : 107010*σ-33609 = 3*(35670*σ-11203) := by ring
  calc
    _ = (3*31544/(3*(35670*σ-11203)))*(1-σ) := by rw [hd]; ring
    _ = (31544/(35670*σ-11203))*(1-σ) := by
      rw [mul_div_mul_left _ _ (by norm_num : (3:ℝ) ≠ 0)]
    _ = _ := div_mul_eq_mul_div _ _ _

end Montgomery.RationalMoment.RightDetector
