module
public import FiniteCutoffOperators
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset InnerProductSpace
open scoped InnerProductSpace
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

/-- The literal finite large-value spectral inequality. The divisor witness,
both Gram positivities, continuous Schur norm, and signed traces are discharged.
This uses the established comparison cutoff with plateau [1,4]. -/
theorem finite_signed_large_value_comparison (w : MathCollab.Density.ComparisonCutoff)
    {η : ℝ} (hη : 0 < η) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧ ∀ N L : ℝ, 0 < N → N ≤ L →
      ∀ a : ℕ → ℂ, (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      ∀ (W : Finset ℝ) (V : ℝ), 0 ≤ V →
      (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (L/(2*N))*(max (((W.card:ℝ)*V^2)/(A*(1+L)^η*(N+1))-D*L) 0)^3 ≤
        (Matrix.trace (cutoffCenteredMatrix w.toReflectionCutoff L W^3)).re+
        (Matrix.trace (cutoffContinuousMatrix w.toReflectionCutoff L W*
          cutoffCenteredMatrix w.toReflectionCutoff L W^2)).re := by
  pm_368
  pm_4555
  pm_76 operator_finite_signed_spectral_comparison
  rw [heH,← finite_matrix_operator_pow,← finite_matrix_operator_pow,
    ← finite_matrix_operator_mul,finite_matrix_operator_trace,finite_matrix_operator_trace] at hspec
  pm_4554
  exact (mul_le_mul_of_nonneg_right hk (pow_nonneg (le_max_right _ _) 3)).trans hspec

end Montgomery.RationalMoment
