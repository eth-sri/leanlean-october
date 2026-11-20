module

public import NearlyMinimax.LowMixtureDerivative
public import NearlyMinimax.LowSmoothnessGridExperiment


@[expose] public section

/-! The design-integrated derivative for the paper's actual grid prior. -/

noncomputable section
open MeasureTheory Set
open scoped Topology BigOperators
namespace NearlyMinimax

def gridSampleField (d k n : ℕ) (η : ℝ) (x : Fin n → Covariate d) :
    (Fin (gridWindowCount d k) → Fin 3) → Fin n → ℝ :=
  fun ξ i => indexedGridField d k η ξ (x i)

section
variable (d k n : ℕ) (η : ℝ)

theorem gridSampleField_measurable :
    Measurable (gridSampleField d k n η) := by
  apply measurable_pi_lambda
  intro ξ
  apply measurable_pi_lambda
  intro i
  have h := (indexedGridField_continuous d k η ξ).measurable.comp
    (show Measurable (fun x : Fin n → Covariate d => x i) from measurable_pi_apply i)
  exact h

theorem gridSampleField_norm_le (hη : 0 ≤ η)
    (x : Fin n → Covariate d) : ‖gridSampleField d k n η x‖ ≤ (2 : ℝ) ^ d * η := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro ξ
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  simpa only [gridSampleField, Real.norm_eq_abs] using indexedGridField_abs_bound d k η hη ξ (x i)

end

def gridMixtureExpectation (d k n : ℕ) (a v η t : ℝ)
    (T : (Fin n → Covariate d) → (Fin n → Fin 3) → ℝ) : ℝ :=
  ∫ x, finiteExperimentExpectation (gridWindowCount d k) n a v η t
    (gridSampleField d k n η x) (T x) ∂Measure.pi (fun _ : Fin n => cubeVolume d)

def gridMixtureScoreObservable (d k n : ℕ) (a v η t : ℝ)
    (T : (Fin n → Covariate d) → (Fin n → Fin 3) → ℝ)
    (x : Fin n → Covariate d) : ℝ :=
  ∑ ξ, activationProductPrior (gridWindowCount d k) t ξ * ∑ y,
    finiteResponseLikelihood (gridWindowCount d k) n a (v - η ^ 2 * t)
      (gridSampleField d k n η x) ξ y * T x y *
    finiteExperimentScore (gridWindowCount d k) n a (v - η ^ 2 * t) η
      (gridSampleField d k n η x) ξ y

section
variable {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ)

theorem grid_response_likelihood_pos (η t : ℝ)
    (hamp : GridAmplitudeBounds d η P.ρ) (ht : t ∈ Icc (0 : ℝ) 1)
    (x : Fin n → Covariate d) (ξ : Fin (gridWindowCount d k) → Fin 3) (y : Fin n → Fin 3) :
    0 < finiteResponseLikelihood (gridWindowCount d k) n P.a (P.v - η ^ 2 * t)
      (gridSampleField d k n η x) ξ y :=
  Finset.prod_pos (fun i _ => grid_response_positive C P k n η t ξ x hamp ht i (y i))

/-- The actual grid-prior mean has the exact integrated score derivative.
Every domination, measurability, and positivity requirement follows from
the grid construction and the original ternary legality neighborhood. -/
theorem grid_mixture_expectation_hasDerivAt (η t M : ℝ)
    (hamp : GridAmplitudeBounds d η P.ρ) (ht : t ∈ Icc (0 : ℝ) 1)
    (T : (Fin n → Covariate d) → (Fin n → Fin 3) → ℝ) (hT : Measurable T)
    (hTBound : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => cubeVolume d), ‖T x‖ ≤ M) :
    HasDerivAt (fun u => gridMixtureExpectation d k n P.a P.v η u T)
      (∫ x, gridMixtureScoreObservable d k n P.a P.v η t T x
        ∂Measure.pi (fun _ : Fin n => cubeVolume d)) t := by
  let _ := cubeVolume_isProbability d
  have hp := grid_response_likelihood_pos C P k n η t hamp ht
  exact finite_experiment_integrated_score_hasDerivAt
    (Measure.pi (fun _ : Fin n => cubeVolume d)) (gridWindowCount d k) n P.a P.v η t
    ((2 : ℝ) ^ d * η) M (gridSampleField d k n η) T
    (gridSampleField_measurable d k n η) hT
    (Filter.Eventually.of_forall (gridSampleField_norm_le d k n η hamp.nonneg)) hTBound
    (Filter.Eventually.of_forall hp)

end

end NearlyMinimax
