module
public import RetunedLongMeanCover
public import QuadraticPolynomialCount
public import DensityWindowBudgets
public import MathCollab.Density.Stronger.ConditionalDensity
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Real Complex Filter MeasureTheory Finset Set
open scoped Topology
set_option maxHeartbeats 2000000
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density GuthMaynard.Improvement

/-- The actual analytic-multiplicity subset detected by the retuned short family. -/
def smoothShortZeroFinset (η σ a δ T : ℝ) : Finset ℂ := by
  classical
  exact (zetaZeroFinset σ T (2*T)).filter (fun ρ =>
    ∃ q ∈ smoothPoweredIndices a δ T,
      (smoothPoweredFamilyScale q:ℝ)^σ*T^(-2*η) ≤
        ‖detectingPolynomial (smoothPoweredFamilyScale q)
          (smoothPoweredFamilyCoefficient η a δ T q) ρ.im‖)

def smoothShortZeroCount (η σ a δ T : ℝ) : ℕ :=
  ∑ ρ ∈ smoothShortZeroFinset η σ a δ T, zetaMultiplicity ρ

theorem smoothShortZeroFinset_subset (η σ a δ T : ℝ) :
    smoothShortZeroFinset η σ a δ T ⊆ zetaZeroFinset σ T (2*T) := by
  classical
  exact filter_subset _ _

/-- All short-detected zeros, with analytic multiplicity, obey the new
quadratic exponent. Every family coefficient and scale is supplied. -/
theorem smoothShortZeroCount_bound {σ a η : ℝ}
    (hw : QuadraticWindow σ a) (hη : 0 < η)
    (hηa : η ≤ (1-3*a/2)/2) (hηg : 9*η < a*(4*σ-3)) (δ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      (smoothShortZeroCount η σ a δ T:ℝ) ≤ C*T^(3*a*(1-σ)+52*η) := by
  classical
  pm_97 C hC hquad quadratic_polynomial_count_loss hw hη hηa hηg
  pm_2773
  filter_upwards [eventually_ge_atTop (2:ℝ),hquad,
    smoothPoweredFamily_admissible hw hη δ,
    smoothPoweredIndices_card_eventually hw δ,
    (tendsto_rpow_atTop hη).eventually_ge_atTop ((2:ℝ)^K),
    log_pow_eventually_le_rpow 3 hη] with T hT hq hadm hJ hconst hlogloss
  pm_2770
  have hper : ∀ q ∈ J, ((Wj q).card:ℝ) ≤ C*T^(3*a*(1-σ)+51*η) := by
    pm_2771
    apply hq (smoothPoweredFamilyScale q:ℝ) T hlo hu (smoothPoweredFamilyCoefficient η a δ T q)
      (fun n _ => hcoeff n) (Wj q)
    pm_2775
  pm_2774
  have hWcard : (W.card:ℝ) ≤ (J.card:ℝ)*(C*T^(3*a*(1-σ)+51*η)) := by
    calc
      _ ≤ ∑ q ∈ J, ((Wj q).card:ℝ) := by exact_mod_cast (Finset.card_le_card hcover).trans card_biUnion_le
      _ ≤ ∑ _q ∈ J, C*T^(3*a*(1-σ)+51*η) := sum_le_sum hper
      _ = _ := by simp
  pm_2772
  have hWcard' : (W.card:ℝ) ≤ (D*(Real.log T)^2)*(C*T^(3*a*(1-σ)+51*η)) :=
    hWcard.trans (mul_le_mul_of_nonneg_right hJ' (by positivity))
  calc
    _ ≤ 2*(Cb*Real.log (2*T))*(W.card:ℝ) := hrestore' 
    _ ≤ 2*(Cb*(2*Real.log T))*((D*(Real.log T)^2)*(C*T^(3*a*(1-σ)+51*η))) := by
      gcongr
    _ = (4*Cb*D*C)*((Real.log T)^3*T^(3*a*(1-σ)+51*η)) := by ring
    _ ≤ (4*Cb*D*C)*(T^η*T^(3*a*(1-σ)+51*η)) := by
      gcongr
    _ = (4*Cb*D*C)*T^(3*a*(1-σ)+52*η) := by rw [← Real.rpow_add hTp]; congr 2; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end Montgomery.RationalMoment.RightDetector
