module
public import LaterPairs.RestrictedPeakTail
public import IntervalExcessTransfer
public import MathCollab.Density.Stronger.SeparatedVolume
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
namespace TaoTrudgianYang2025
open MathCollab.Density MathCollab.Density.Stronger
open Montgomery.RationalMoment.RightDetector

theorem ExponentPair.critical_slab_excess_general {k l η ε : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k)
    (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ v : ℝ, 0 < v → H^(1/8+η) ≤ v →
      (∫ t in Icc H (2*H),criticalExcess v t) ≤
        (2/5)*H^(1+ε)*v^(-5:ℝ)+
          (2/(3+(2+4*l)/k))*H^(1+l/k+ε)*v^(-3-(2+4*l)/k) := by
  pm_362
  filter_upwards [hpair.restricted_critical_peak_tail_general hk hη hε,
    eventually_ge_atTop (1:ℝ)] with H hsource hH
  pm_70
end TaoTrudgianYang2025
