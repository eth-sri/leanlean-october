module

public import Mathlib
public import PottsDiscontinuity.SixVertex.Cor34BethePF
public import PottsDiscontinuity.SixVertex.Cor34FinalEigen

/-! # Corollary 3.4: normalize Theorem 3.1 for the infinite-anisotropy branch -/

public section

open Matrix
open scoped BigOperators

namespace PottsDiscontinuity.SixVertex

section
variable {N n : ℕ} {ε : ℝ} (hε : ε < 0)
include ε hε
theorem cor34_final_normalizedTransferBlock_scale  :
    cor34_normalizedTransferBlock N n ε =
      (-ε / 2) ^ n • transferBlock N (Real.sqrt (2 - 2 / ε)) n := by
  rw [cor34_normalizedTransferBlock_eq_scaled_transferBlock ε hε]
  have hbase : ((-2 / ε : ℝ)⁻¹) = -ε / 2 := by
    grind
  have hpow : ((-2 / ε : ℝ) ^ n)⁻¹ = (-ε / 2) ^ n := by
    rw [← inv_pow, hbase]
  simp_all

theorem cor34_final_normalizedBlockWave_scale (p : Fin n → ℝ) :
    cor34_normalizedBlockWave (N := N) ε p =
      (((-ε / 2 : ℝ) : ℂ) ^ cor34_pairCount n) •
        BetheAnsatz.blockWave (N := N) (1 / ε) p := by
  funext x
  change cor34_normalizedCoordinate ε p (BetheAnsatz.positions x) = _
  rw [cor34_normalizedCoordinate_eq_scaled_coordinateWave ε p
    (BetheAnsatz.positions x) (ne_of_lt hε)]
  rfl
end

theorem cor34_final_scale_eigen_equation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} {v : ι → ℂ} {μ a b : ℂ}
    (hEig : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    (a • A.map (algebraMap ℝ ℂ)) *ᵥ (b • v) = (a * μ) • (b • v) := by
  ext i
  have hi := congrFun hEig i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi ⊢
  calc
    (∑ j, (a * A i j) * (b * v j)) =
        a * b * ∑ j, A i j * v j := by
          calc
            _ = ∑ j, (a * b) * (A i j * v j) := by
              grind
            _ = _ := by rw [Finset.mul_sum]
    _ = a * b * (μ * v i) := by simp_all
    _ = (a * μ) * (b * v i) := by ring

end PottsDiscontinuity.SixVertex
