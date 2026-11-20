module

public import NearlyMinimax.PopulationMomentDerivatives

@[expose] public section

/-! Scalar feature-row derivative bounds for the actual population inverse pilots. -/

noncomputable section
namespace NearlyMinimax
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

def rowFunctional {r : ℕ} (row : Fin r → ℝ) : (Fin r → ℝ) →L[ℝ] ℝ :=
  ∑ i, row i • (ContinuousLinearMap.proj i : (Fin r → ℝ) →L[ℝ] ℝ)

section
variable {r : ℕ}

@[simp] theorem rowFunctional_apply (row z : Fin r → ℝ) :
    rowFunctional row z = row ⬝ᵥ z := by
  simp [rowFunctional, dotProduct, smul_eq_mul]

theorem rowFunctional_norm_le (row : Fin r → ℝ) :
    ‖rowFunctional row‖ ≤ ∑ i, |row i| := by
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  intro z
  rw [rowFunctional_apply, dotProduct]
  calc
    ‖∑ i, row i * z i‖ ≤ ∑ i, ‖row i * z i‖ := norm_sum_le _ _
    _ ≤ ∑ i, |row i| * ‖z‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z i) (abs_nonneg _)
    _ = (∑ i, |row i|) * ‖z‖ := by rw [Finset.sum_mul]

end

def incrementFinScalar (r : ℕ) (lo hi : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (row : Fin r → ℝ) :
    (Fin (Fintype.card (incrementVariables r)) → ℝ) → ℝ :=
  fun x => row ⬝ᵥ incrementFinVector r lo hi T y m x

theorem incrementFinScalar_iteratedFDeriv (r : ℕ) [NeZero r] (lo hi : ℝ)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m k : ℕ) (row : Fin r → ℝ)
    (x : Fin (Fintype.card (incrementVariables r)) → ℝ)
    (v : Fin k → Fin (Fintype.card (incrementVariables r)) → ℝ) :
    iteratedFDeriv ℝ k (incrementFinScalar r lo hi T y m row) x v =
      rowFunctional row (iteratedFDeriv ℝ k (incrementFinVector r lo hi T y m) x v) := by
  have h := (rowFunctional row).iteratedFDeriv_comp_left (x := x)
    (incrementFinVector_contDiff r lo hi T y m).contDiffAt (show (k : WithTop ℕ∞) ≤ ⊤ from le_top)
  have hFun : (rowFunctional row) ∘ incrementFinVector r lo hi T y m =
      incrementFinScalar r lo hi T y m row := by
    funext z
    exact rowFunctional_apply row _
  simp_all

end NearlyMinimax
