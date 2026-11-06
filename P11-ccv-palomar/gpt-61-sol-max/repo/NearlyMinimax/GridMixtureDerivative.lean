module

public import NearlyMinimax.LowMixtureDerivative
public import NearlyMinimax.LowSmoothnessGridExperiment


@[expose] public section

/-! The design-integrated derivative for the paper's actual grid prior. -/

noncomputable section
open MeasureTheory Set
open scoped Topology BigOperators
namespace NearlyMinimax

section
variable (d k n : ℕ)
include k

def gridSampleField  η (x : Fin n → Covariate d)  :=
  fun ξ i => indexedGridField d k η ξ (x i)

theorem gridSampleField_measurable  η :
    Measurable (gridSampleField d k n η) := by
  apply measurable_pi_lambda
  intro ξ
  apply measurable_pi_lambda
  intro i
  have h := (indexedGridField_continuous d k η ξ).measurable.comp
    (show Measurable (fun x : Fin n → Covariate d => x i) from measurable_pi_apply i)
  exact h

theorem gridSampleField_norm_le  η (hη : 0 ≤ η)
    x : ‖gridSampleField d k n η x‖ ≤ 2 ^ d * η := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro ξ
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  
  solve_by_elim [indexedGridField_abs_bound]

section
variable (a v η t : ℝ) (T : (Fin n → Covariate d) → (Fin n → Fin 3) → ℝ)
include a v η t T

def gridMixtureExpectation    :=
  ∫ x, finiteExperimentExpectation (gridWindowCount d k) n a v η t
    (gridSampleField d k n η x) (T x) ∂Measure.pi (fun _ : Fin n => cubeVolume d)

def gridMixtureScoreObservable  
    x  :=
  ∑ ξ, activationProductPrior (gridWindowCount d k) t ξ * ∑ y,
    finiteResponseLikelihood (gridWindowCount d k) n a (v - η ^ 2 * t)
      (gridSampleField d k n η x) ξ y * T x y *
    finiteExperimentScore (gridWindowCount d k) n a (v - η ^ 2 * t) η
      (gridSampleField d k n η x) ξ y
end

end


section
variable {d : ℕ} (C : ModelConstants d) (P : LowSmoothnessTernaryConstants C)

theorem grid_response_likelihood_pos  k n η t
    (hη : 0 ≤ η) (ht : t ∈ Icc 0 1)
    (hfield : (2 ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    x ξ y :
    0 < finiteResponseLikelihood (gridWindowCount d k) n P.a (P.v - η ^ 2 * t)
      (gridSampleField d k n η x) ξ y := by
  have hBase : (2 : ℝ) ^ d * η ≤ P.ρ := by nlinarith
  
  apply Finset.prod_pos
  intro i _
  have hAbs  :=
    (indexedGridField_abs_bound d k η hη ξ (x i)).trans hBase
  exact P.c_pos.trans_le ((P.path_legality η t _ ht hvariance hAbs).2.2.1 (y i))

/-- The actual grid-prior mean has the exact integrated score derivative.
Every domination, measurability, and positivity requirement follows from
the grid construction and the original ternary legality neighborhood. -/
theorem grid_mixture_expectation_hasDerivAt  k n η t M
    (hη : 0 ≤ η) (ht : t ∈ Icc 0 1)
    (hfield : (2 ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    T (hT : Measurable T)
    (hTBound : ∀ᵐ x ∂Measure.pi (fun _  => cubeVolume d), ‖T x‖ ≤ M) :
    Integrable (gridMixtureScoreObservable d k n P.a P.v η t T)
        (Measure.pi (fun _  => cubeVolume d)) ∧
      HasDerivAt (fun u => gridMixtureExpectation d k n P.a P.v η u T)
        (∫ x, gridMixtureScoreObservable d k n P.a P.v η t T x
          ∂Measure.pi (fun _  => cubeVolume d)) t := by
  let _ := cubeVolume_isProbability d
  have hp  := grid_response_likelihood_pos C P k n η t hη ht hfield hvariance
  exact finite_experiment_integrated_score_hasDerivAt
    (Measure.pi (fun _ : Fin n => cubeVolume d)) (gridWindowCount d k) n P.a P.v η t
    ((2 : ℝ) ^ d * η) M (gridSampleField d k n η) T
    (gridSampleField_measurable d k n η) hT
    (Filter.Eventually.of_forall (gridSampleField_norm_le d k n η hη)) hTBound
    (Filter.Eventually.of_forall hp)
end


theorem grid_mixture_raw_derivative_continuous d k n a v η M (hη : 0 ≤ η)
    T (hT : Measurable T)
    (hTBound : ∀ᵐ x ∂Measure.pi (fun _  => cubeVolume d), ‖T x‖ ≤ M) :
    Continuous (fun t => ∫ x, finiteExperimentRawDerivative (gridWindowCount d k) n a v η t
      (gridSampleField d k n η x) (T x) ∂Measure.pi (fun _  => cubeVolume d)) := by
  let _ := cubeVolume_isProbability d
  exact finite_experiment_integrated_raw_derivative_continuous
    (Measure.pi (fun _ : Fin n => cubeVolume d)) (gridWindowCount d k) n a v η ((2 : ℝ) ^ d * η) M
    (gridSampleField d k n η) T (gridSampleField_measurable d k n η) hT
    (Filter.Eventually.of_forall (gridSampleField_norm_le d k n η hη)) hTBound

/-- The score-observable derivative along the actual probability path is
interval integrable, with no regularity assumption on the bounded observable. -/
theorem grid_mixture_score_observable_intervalIntegrable {d } (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) k n η M
    (hη : 0 ≤ η) (hfield : (2 ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    T (hT : Measurable T)
    (hTBound : ∀ᵐ x ∂Measure.pi (fun _  => cubeVolume d), ‖T x‖ ≤ M) :
    IntervalIntegrable (fun t => ∫ x, gridMixtureScoreObservable d k n P.a P.v η t T x
      ∂Measure.pi (fun _  => cubeVolume d)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  apply (grid_mixture_raw_derivative_continuous d k n P.a P.v η M hη T hT hTBound).continuousOn.congr
  intro t ht
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  exact (finite_experiment_raw_derivative_eq_score (gridWindowCount d k) n P.a P.v η t
    (gridSampleField d k n η x) (T x)
    (grid_response_likelihood_pos C P k n η t hη ht hfield hvariance x)).symm

end NearlyMinimax
