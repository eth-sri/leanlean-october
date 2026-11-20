module

public import NearlyMinimax.GridMixtureDerivative


@[expose] public section

/-! Measurability and integrated square-root score budget for the actual grid path. -/

noncomputable section
open MeasureTheory Set
open scoped Topology BigOperators
namespace NearlyMinimax

theorem grid_prior_score_energy_path_measurable (d k n : ℕ) (a v η : ℝ) :
    Measurable (gridPriorScoreEnergy d k n a v η) := by
  let _ := cubeVolume_isProbability d
  apply Finset.measurable_sum
  intro ξ _
  have hPrior  :=
    (continuous_iff_continuousAt.mpr (fun t =>
      (activation_product_prior_hasDerivAt t ξ).continuousAt)).measurable
  have hInt := (grid_score_energy_measurable_comp a η ξ
    (V := fun z : ℝ × (DesignSample d n) => v - η ^ 2 * z.1) (by fun_prop) measurable_snd).stronglyMeasurable.integral_prod_right'
    (ν := Measure.pi (fun _ => cubeVolume d))
  exact hPrior.mul hInt.measurable

def gridUniformScoreBudget {d : ℕ} {C : ModelConstants d}
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η : ℝ) : ℝ :=
  40 ^ d * ternaryScoreExponentialConstant P.a P.ρ P.c ^ 2 *
    Real.exp (ternaryScoreExponentialConstant P.a P.ρ P.c) * n ^ 2 * η ^ 4 / k ^ d

variable {d : ℕ} {C : ModelConstants d} {P : LowSmoothnessTernaryConstants C} {k n : ℕ} {η : ℝ}
    (hk : 1 ≤ k) (hη : 0 ≤ η) (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (hmean : n * (2 / (k : ℝ)) ^ d ≤ 1)
include hfield hk hmean hvariance hη

theorem grid_sqrt_score_energy_intervalIntegrable :
    IntervalIntegrable (fun t => Real.sqrt (gridPriorScoreEnergy d k n P.a P.v η t)) volume 0 1 := by
  have hMeas : Measurable (fun t => Real.sqrt (gridPriorScoreEnergy d k n P.a P.v η t)) :=
    Real.continuous_sqrt.measurable.comp (grid_prior_score_energy_path_measurable ..)
  have hI : IntegrableOn (fun t => Real.sqrt (gridPriorScoreEnergy d k n P.a P.v η t)) (Icc 0 1) volume := by
    apply Integrable.of_bound hMeas.aestronglyMeasurable (Real.sqrt (gridUniformScoreBudget P k n η))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    bound [grid_prior_score_energy_bound hk hη ht hfield hvariance hmean]
  apply IntegrableOn.intervalIntegrable
  simpa using hI

theorem grid_sqrt_score_energy_integral_le :
    (∫ t in 0..1, Real.sqrt (gridPriorScoreEnergy d k n P.a P.v η t)) ≤
      Real.sqrt (gridUniformScoreBudget P k n η) := by
  have h := intervalIntegral.integral_mono_on (by norm_num) (grid_sqrt_score_energy_intervalIntegrable hk hη hfield hvariance hmean)
    (intervalIntegrable_const : IntervalIntegrable (fun _ => Real.sqrt (gridUniformScoreBudget P k n η)) volume 0 1)
    (fun t ht => Real.sqrt_le_sqrt (grid_prior_score_energy_bound hk hη ht hfield hvariance hmean))
  simpa using h

end NearlyMinimax
