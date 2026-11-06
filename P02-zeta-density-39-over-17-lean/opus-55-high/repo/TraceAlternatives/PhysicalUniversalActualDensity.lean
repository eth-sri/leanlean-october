module
public import LaterPairs.PhysicalPairLongZeroCount
public import TraceAlternatives.PhysicalUniversalShortZeroCount
public import RetunedActualDensity
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
noncomputable section
open Real Filter MeasureTheory Set
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger MathCollab.Density TaoTrudgianYang2025

/-- Actual zeta zeros from a genuine analytic pair, with every detector and
tail input discharged. The two exact exponent budgets are numerical. -/
theorem density_of_pair_universal_window {k l σ a ε : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k)
    (hw : PhysicalDetectorWindow σ a) (hc : UniversalCountWindow σ a)
    (hfirst : 1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ))
    (hsecond : 1+l/k-(4+(2+4*l)/k)*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ))
    (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3*a*(1-σ)+ε) := by
  have hthreshold := hw.threshold
  pm_510
  pm_270
  pm_1604
  pm_81
  let η : ℝ := min (1/3600) (min (ε/1000) (min ((1-3*a/2)/4) (a*(4*σ-3)/100)))
  pm_2755
  pm_1274
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min (by norm_num) (lt_min (by positivity) (lt_min (by linarith [hw.a_high]) (by positivity)))
  have hηsmall : η ≤ 1/3600 := min_le_left _ _
  have hηeps : η ≤ ε/1000 := (min_le_right _ _).trans (min_le_left _ _)
  have hηa : η ≤ (1-3*a/2)/4  := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨Cs,hCs,hshort⟩ := smoothShortZeroCount_universal_bound hw hc hη (by linarith)
    (by linarith [hw.a_high]) δ
  obtain ⟨Cl,hCl,hlong⟩ := smoothLongZeroCount_pair_tail_general hpair hk hw
    hδ (by linarith) hη (show 0 < ε/2 by positivity) hq hmargin
    (show 1-6*q ≤ 3*a*(1-σ)+(ε/2)/2 by dsimp [q,θ] at *; linarith)
    (show 1+l/k-(4+(2+4*l)/k)*q ≤ 3*a*(1-σ)+(ε/2)/2 by
      pm_644
      nlinarith)
  have hslab : ∀ᶠ T : ℝ in atTop,
      (zetaSlabCount σ T (2*T):ℝ) ≤ (Cs+Cl)*T^(3*a*(1-σ)+ε) := by
    filter_upwards [hshort,hlong,eventually_ge_atTop (1:ℝ)] with T hsT hlT hT
    have hs' := hsT.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT (show 3*a*(1-σ)+145*η ≤ 3*a*(1-σ)+ε by linarith)) hCs.le)
    pm_285
  pm_259
end Montgomery.RationalMoment.RightDetector.Physical
