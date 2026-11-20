module

public import NearlyMinimax.PopulationMomentDerivatives

@[expose] public section

/-! Scalar feature-row derivative bounds for the actual population inverse pilots. -/

noncomputable section
namespace NearlyMinimax
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

section
variable {r : ℕ} (lo hi : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) (row : Fin r → ℝ)

def rowFunctional : (Fin r → ℝ) →L[ℝ] ℝ :=
  ∑ i, row i • (ContinuousLinearMap.proj i)

@[simp] theorem rowFunctional_apply (z : Fin r → ℝ) :
    rowFunctional row z = row ⬝ᵥ z := by
  simp [rowFunctional, dotProduct]

theorem rowFunctional_norm_le :
    ‖rowFunctional row‖ ≤ ∑ i, |row i| := by
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  intro z
  rw [rowFunctional_apply]
  calc
    _ ≤ _ := norm_sum_le _ _
    _ ≤ ∑ i, |row i| * ‖z‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z i) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

def incrementFinScalar :
    (Fin (Fintype.card (incrementVariables r)) → ℝ) → ℝ :=
  fun x => row ⬝ᵥ incrementFinVector r lo hi T y m x

end

theorem incrementFinScalar_iteratedFDeriv (r : ℕ) [NeZero r] (lo hi : ℝ)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m k : ℕ) (row : Fin r → ℝ)
    (x : Fin (Fintype.card (incrementVariables r)) → ℝ)
    (v : Fin k → Fin (Fintype.card (incrementVariables r)) → ℝ) :
    iteratedFDeriv ℝ k (incrementFinScalar lo hi T y m row) x v =
      rowFunctional row (iteratedFDeriv ℝ k (incrementFinVector r lo hi T y m) x v) := by
  have h := (rowFunctional row).iteratedFDeriv_comp_left (x := x)
    (incrementFinVector_contDiff r lo hi T y m).contDiffAt (show (k : WithTop ℕ∞) ≤ ⊤ from le_top)
  have hFun : (rowFunctional row) ∘ incrementFinVector r lo hi T y m =
      incrementFinScalar lo hi T y m row := by
    funext z
    exact rowFunctional_apply row _
  simp_all

end NearlyMinimax
