module
public import TraceAlternatives.PhysicalUniversalActualDensity
public import LaterPairs.NativeTTY3
public import LaterPairs.TTY4TargetParameters
public import LaterPairs.PhysicalTargetWindows
public import LaterPairs.NativeTTY4Prefix
public import RightSolidTailBudgets

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density

theorem density_cube_row3 {σ ε : ℝ}
    (hlo : 163/198 ≤ σ) (hhi : σ ≤ 7873/9370) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(31544*(1-σ)/(35670*σ-11203)+ε) :=
  density_of_pair_universal_fraction TaoTrudgianYang2025.exponentPair_BTTY4 hε

