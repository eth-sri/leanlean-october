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
variable (d k n : ℕ) (a v η t : ℝ) (T : (DesignSample d n) → (TernaryVector n) → ℝ)

def gridSampleField (x : DesignSample d n) :
    (TernaryVector (gridWindowCount d k)) → Fin n → ℝ :=
  fun ξ i => indexedGridField η ξ (x i)

theorem gridSampleField_measurable :
    Measurable (gridSampleField d k n η) := by
  exact measurable_pi_lambda fun ξ => measurable_pi_lambda fun i => Measurable.comp (Continuous.measurable (indexedGridField_continuous η ξ)) (have this := measurable_pi_apply i; this)

theorem gridSampleField_norm_le {η : ℝ} (hη : 0 ≤ η)
    (x : DesignSample d n) : ‖gridSampleField d k n η x‖ ≤ 2 ^ d * η := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro ξ
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  solve_by_elim [indexedGridField_abs_bound]

def gridMixtureExpectation : ℝ :=
  ∫ x, finiteExperimentExpectation a v η t
    (gridSampleField d k n η x) (T x) ∂Measure.pi (fun _ => cubeVolume d)

def gridMixtureScoreObservable
    (x : DesignSample d n) : ℝ :=
  ∑ ξ, activationProductPrior t ξ * ∑ y,
    finiteResponseLikelihood a (v - η ^ 2 * t)
      (gridSampleField d k n η x) ξ y * T x y *
    finiteExperimentScore a (v - η ^ 2 * t) η
      (gridSampleField d k n η x) ξ y

end

section
variable {d : ℕ} {C : ModelConstants d} {P : LowSmoothnessTernaryConstants C} (k n : ℕ) {η t M : ℝ}
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1) (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ)
    (hvariance : η ^ 2 ≤ P.ρ)
include hη ht hfield hvariance

theorem grid_response_likelihood_pos
    (x : DesignSample d n) (ξ : TernaryVector (gridWindowCount d k)) (y : TernaryVector n) :
    0 < finiteResponseLikelihood P.a (P.v - η ^ 2 * t)
      (gridSampleField d k n η x) ξ y := by
  apply Finset.prod_pos
  intro i _
  exact P.c_pos.trans_le ((P.path_legality η t _ ht hvariance ((indexedGridField_abs_bound hη ξ (x i)).trans (by nlinarith))).2.2.1 (y i))

/-- The actual grid-prior mean has the exact integrated score derivative.
Every domination, measurability, and positivity requirement follows from
the grid construction and the original ternary legality neighborhood. -/
theorem grid_mixture_expectation_hasDerivAt
    {T : (DesignSample d n) → (TernaryVector n) → ℝ} (hT : Measurable T)
    (hTBound : ∀ᵐ x ∂Measure.pi (fun _ => cubeVolume d), ‖T x‖ ≤ M) :
    Integrable (gridMixtureScoreObservable d k n P.a P.v η t T)
        (Measure.pi (fun _ => cubeVolume d)) ∧
      HasDerivAt (fun u => gridMixtureExpectation d k n P.a P.v η u T)
        (∫ x, gridMixtureScoreObservable d k n P.a P.v η t T x
          ∂Measure.pi (fun _ => cubeVolume d)) t := by
  exact let x := cubeVolume_isProbability d; finite_experiment_integrated_score_hasDerivAt (Measure.pi fun x => cubeVolume d) (gridSampleField_measurable d k n η) hT (Filter.Eventually.of_forall (gridSampleField_norm_le d k n hη)) hTBound (Filter.Eventually.of_forall (grid_response_likelihood_pos k n hη ht hfield hvariance))

end

theorem grid_mixture_raw_derivative_continuous (d k n : ℕ) (a v η M : ℝ) (hη : 0 ≤ η)
    {T : (DesignSample d n) → (TernaryVector n) → ℝ} (hT : Measurable T)
    (hTBound : ∀ᵐ x ∂Measure.pi (fun _ => cubeVolume d), ‖T x‖ ≤ M) :
    Continuous (fun t => ∫ x, finiteExperimentRawDerivative a v η t
      (gridSampleField d k n η x) (T x) ∂Measure.pi (fun _ => cubeVolume d)) := by
  let _ := cubeVolume_isProbability d
  exact finite_experiment_integrated_raw_derivative_continuous
    (Measure.pi (fun _ => cubeVolume d)) a v η (gridSampleField_measurable ..) hT
    (Filter.Eventually.of_forall (gridSampleField_norm_le d k n hη)) hTBound

/-- The score-observable derivative along the actual probability path is
interval integrable, with no regularity assumption on the bounded observable. -/
theorem grid_mixture_score_observable_intervalIntegrable {d : ℕ} {C : ModelConstants d}
    {P : LowSmoothnessTernaryConstants C} (k n : ℕ) {η M : ℝ}
    (hη : 0 ≤ η) (hfield : (2 ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    {T : (DesignSample d n) → (TernaryVector n) → ℝ} (hT : Measurable T)
    (hTBound : ∀ᵐ x ∂Measure.pi (fun _ => cubeVolume d), ‖T x‖ ≤ M) :
    IntervalIntegrable (fun t => ∫ x, gridMixtureScoreObservable d k n P.a P.v η t T x
      ∂Measure.pi (fun _ => cubeVolume d)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  apply (grid_mixture_raw_derivative_continuous d k n P.a P.v η M hη hT hTBound).continuousOn.congr
  intro t ht
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  exact Eq.symm (finite_experiment_raw_derivative_eq_score (T x) (grid_response_likelihood_pos k n hη ht hfield hvariance x))

end NearlyMinimax
