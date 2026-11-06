module
public import PairSlabExcess
public import TwoTermDyadic
public import ExcessCompactPrefix
public import LaterPairs.PairPhysicalExcess

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
namespace TaoTrudgianYang2025
open MathCollab.Density MathCollab.Density.Stronger
open Montgomery.CriticalPeak Montgomery.RationalMoment.RightDetector

/-- Both physical excess terms, with constants uniform before height and amplitude. -/
theorem ExponentPair.critical_physical_excess {k l η ε : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k) (hlog : 2+4*l/k ≤ 7)
    (hη : 0 < η) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ v : ℝ,
      0 < v → (3*T)^(1/8+η) ≤ v →
      (∫ t in Icc 0 (3*T),criticalExcess v t) ≤
        C*T^ε*(T*v^(-5:ℝ)+T^(1+l/k)*v^(-3-(2+4*l)/k)) :=
  hpair.critical_physical_excess_general hk hη hε

end TaoTrudgianYang2025
