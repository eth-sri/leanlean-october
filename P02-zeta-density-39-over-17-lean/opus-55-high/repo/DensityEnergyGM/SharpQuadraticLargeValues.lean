module
public import QuadraticAmplifiedMoment
public import DensityEnergyGM.SharpCenteredTrace
public import TraceAlternatives.CubeQuadraticLargeValues
import WeylPort.Analytic.RealLaplace

public section

open Finset
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

/-- The actual quadratic amplifier with the sharp reflected trace.
Every analytic input is supplied, with the original closed ordered energy. -/
theorem finite_quadratic_large_value_sharp (w : MathCollab.Density.ComparisonCutoff)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N L : ℝ,
      2 ≤ T → 1 ≤ N → N ≤ L → Real.sqrt T ≤ L → L ≤ T →
      ∀ a : ℕ → ℂ, (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      ∀ (W : Finset ℝ) (V : ℝ), 0 ≤ V →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (W.card:ℝ)^2*V^4 ≤ C*T^η*((N*L)^2+
        (N^3/L)*sharpCenteredBudget T L W.card (discreteAdditiveEnergy W)) := by pm_2734 centered_trace_sharp sharpCenteredBudget_nonneg sharpCenteredBudget

/-- The three sharp physical powers from the actual quadratic amplifier,
with the proved broad comparison cutoff supplied internally. -/
theorem finite_quadratic_large_value_sharp_native
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N L : ℝ,
      2 ≤ T → 1 ≤ N → N ≤ L → Real.sqrt T ≤ L → L ≤ T →
      ∀ a : ℕ → ℂ, (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      ∀ (W : Finset ℝ) (V : ℝ), 0 ≤ V →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (W.card:ℝ)^2*V^4 ≤ C*T^η*((N*L)^2+
        N^3*T/L*(discreteAdditiveEnergy W:ℝ)^(1/2:ℝ)+
        N^3*T^(4/5:ℝ)*L^(-4/5:ℝ)*(W.card:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/4:ℝ)+
        N^3*T^(9/20:ℝ)*L^(-1/5:ℝ)*(W.card:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/4:ℝ)) := by
  pm_8728 finite_quadratic_large_value_sharp
  pm_2735
  have hFour : L^(1/5:ℝ)/L=L^(-4/5:ℝ) := by
    have h := (Real.rpow_sub hLp (1/5:ℝ) 1).symm
    norm_num at h
    simpa only [neg_div] using h
  have hOne : L^(4/5:ℝ)/L=L^(-1/5:ℝ) := by
    have h := (Real.rpow_sub hLp (4/5:ℝ) 1).symm
    norm_num at h
    simpa only [neg_div] using h
  exact h.trans_eq (by
    unfold sharpCenteredBudget
    rw [← hFour,← hOne]
    ring)


end Montgomery.RationalMoment
