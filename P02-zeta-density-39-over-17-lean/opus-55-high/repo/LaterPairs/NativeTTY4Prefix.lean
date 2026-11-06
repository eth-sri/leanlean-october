module
public import LaterPairs.NativeTTY4
public import LaterPairs.TTY4TargetParameters
public import LaterPairs.PairActualDensity

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density

theorem tty4_prefix_density_exponent {σ : ℝ} :
    3*(31544/(107010*σ-33609))*(1-σ) =
      31544*(1-σ)/(35670*σ-11203) := by grind

end Montgomery.RationalMoment.RightDetector
