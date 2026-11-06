module
public import TwoPowerTailTransfer
public import MathCollab.Density.Stronger.LongScalarBudget
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Real Complex Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density

/-- The exact actual critical-mean detection threshold. -/
def criticalMeanThreshold (C σ a δ T : ℝ) : ℝ :=
  (detectorY a T)^((σ-1/2)/2)/(48*C*Real.sqrt (detectorX δ T)*Real.log T)

theorem criticalMeanThreshold_eventually {C σ a δ : ℝ}
    (hC : 0 < C) (hw : QuadraticWindow σ a) (hsigma : 7/9 ≤ σ)
    (hδ : δ ≤ 1/8) :
    ∀ᶠ T : ℝ in atTop,
      1 ≤ criticalMeanThreshold C σ a δ T ∧
        48*Real.pi*T^(-125:ℝ) ≤ criticalMeanThreshold C σ a δ T := by
  pm_4879
  pm_4336
  pm_390 hlogp T
  pm_5306 hXp detectorX δ hTp
  pm_4878
  have hexp : δ/2+1/48 ≤ (3*a/4)*(σ-1/2) := by
    have hprod := mul_nonneg (show 0 ≤ a-1/2 by linarith [hw.a_low])
      (show 0 ≤ σ-7/9 by linarith)
    nlinarith [hw.a_low]
  pm_4877

/-- Every complementary actual zero, with its analytic multiplicity, is
counted by the literal critical-zeta excess integral. No zeta-tail or
moment bound is a premise; this isolates the missing physical tail producer. -/
theorem smoothLongZeroCount_excess_reduction {σ a δ η : ℝ}
    (hw : QuadraticWindow σ a) (hsigma : 7/9 ≤ σ)
    (hδ : 0 < δ) (hδcap : δ ≤ 1/8) (hη : 0 < η) :
    ∃ C D : ℝ,0 < C ∧ 0 < D ∧ ∀ᶠ T : ℝ in atTop,
      (smoothLongZeroCount η σ a δ T:ℝ)*criticalMeanThreshold C σ a δ T ≤
        D*Real.log T*(∫ t in Icc 0 (3*T),
          criticalExcess (criticalMeanThreshold C σ a δ T/(4*Real.pi)) t) := by
  classical
  obtain ⟨Cm,hCm,hmean⟩ := smoothLongZeroFinset_eventually_detects_mean hw hsigma hδ hδcap hη
  pm_4881
  filter_upwards [eventually_ge_atTop (2:ℝ),hmean,
    criticalMeanThreshold_eventually hCm hw hsigma hδcap] with T hT hm hb
  pm_4880

end Montgomery.RationalMoment.RightDetector
