module
public import LaterPairs.PhysicalLongMeanCover
public import RetunedShortZeroCount
public import TraceAlternatives.UniversalPolynomialCountWindows
import WeylPort.Analytic.RealLaplace

public section

open Real Complex Filter MeasureTheory Finset Set
open scoped Topology
set_option maxHeartbeats 2400000
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger MathCollab.Density GuthMaynard.Improvement

/-- All actual short-detected zeros with analytic multiplicity, using the
proved sharp trace and full energy. The exact perturbation loss is145eta. -/
theorem smoothShortZeroCount_universal_bound {σ a η : ℝ}
    (hw : PhysicalDetectorWindow σ a) (hc : UniversalCountWindow σ a) (hη : 0 < η)
    (hηsmall : η ≤ 1/1800) (hηa : η ≤ (1-3*a/2)/2) (δ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      (smoothShortZeroCount η σ a δ T:ℝ) ≤ C*T^(3*a*(1-σ)+145*η) := by
  classical
  obtain ⟨C,T₀,hC,hT₀,hquad⟩ := universal_polynomial_count_window_loss hc hη hηsmall hηa
  pm_2773
  filter_upwards [eventually_ge_atTop T₀,
    smoothPoweredFamily_admissible hw hη δ,
    smoothPoweredIndices_card_eventually hw δ,
    (tendsto_rpow_atTop hη).eventually_ge_atTop ((2:ℝ)^K),
    log_pow_eventually_le_rpow 3 hη] with T hTall hadm hJ hconst hlogloss
  have hT : 2 ≤ T := hT₀.trans hTall
  pm_2770
  have hper : ∀ q ∈ J, ((Wj q).card:ℝ) ≤ C*T^(3*a*(1-σ)+144*η) := by
    pm_2771
    apply hquad T T (smoothPoweredFamilyScale q:ℝ) hTall hlo hu (smoothPoweredFamilyCoefficient η a δ T q)
      (fun n _ => hcoeff n) (Wj q)
    pm_2775
  pm_2774
  have hWcard : (W.card:ℝ) ≤ (J.card:ℝ)*(C*T^(3*a*(1-σ)+144*η)) := by
    calc
      _ ≤ ∑ q ∈ J, ((Wj q).card:ℝ) := by exact_mod_cast (Finset.card_le_card hcover).trans card_biUnion_le
      _ ≤ ∑ _q ∈ J, C*T^(3*a*(1-σ)+144*η) := sum_le_sum hper
      _ = _ := by simp
  pm_2772
  have hWcard' : (W.card:ℝ) ≤ (D*(Real.log T)^2)*(C*T^(3*a*(1-σ)+144*η)) :=
    hWcard.trans (mul_le_mul_of_nonneg_right hJ' (by positivity))
  calc
    _ ≤ 2*(Cb*Real.log (2*T))*(W.card:ℝ) := hrestore' 
    _ ≤ 2*(Cb*(2*Real.log T))*((D*(Real.log T)^2)*(C*T^(3*a*(1-σ)+144*η))) := by
      gcongr
    _ = (4*Cb*D*C)*((Real.log T)^3*T^(3*a*(1-σ)+144*η)) := by ring
    _ ≤ (4*Cb*D*C)*(T^η*T^(3*a*(1-σ)+144*η)) := by
      gcongr
    _ = (4*Cb*D*C)*T^(3*a*(1-σ)+145*η) := by rw [← Real.rpow_add hTp]; congr 2; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end Montgomery.RationalMoment.RightDetector.Physical
