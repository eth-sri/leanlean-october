module

public import Mathlib
public import PottsDiscontinuity.SixVertex.Cor34BethePF
public import PottsDiscontinuity.SixVertex.Cor34FinalEigen

@[expose] public section

open Matrix
open scoped BigOperators

namespace PottsDiscontinuity.SixVertex

private theorem cor34_final_scale_eigen_equation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} {v : ι → ℂ} {μ a b : ℂ}
    (hEig : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    (a • A.map (algebraMap ℝ ℂ)) *ᵥ (b • v) = (a * μ) • (b • v) := by
  ext i
  have hi := congrFun hEig i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi ⊢
  change (∑ j, (a * (A i j : ℂ)) * (b * v j)) = (a * μ) * (b * v i)
  have hi' : (∑ j, (A i j : ℂ) * v j) = μ * v i := hi
  calc (∑ j, (a * (A i j : ℂ)) * (b * v j))
    _ = (a * b) * ∑ j, (A i j : ℂ) * v j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    _ = (a * μ) * (b * v i) := by rw [hi']; ring

private theorem cor34_final_normalized_eigen_of_raw {N n : ℕ} {ε : ℝ}
    (hε : ε < 0) (p : Fin n → ℝ) {Λ normΛ : ℂ}
    (hraw : (transferBlock N (Real.sqrt (2 - 2 / ε)) n).map (algebraMap ℝ ℂ) *ᵥ
        BetheAnsatz.blockWave (N := N) (1 / ε) p =
      Λ • BetheAnsatz.blockWave (N := N) (1 / ε) p)
    (hscale : normΛ = (((-ε / 2 : ℝ) : ℂ) ^ n) * Λ) :
    (cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ) *ᵥ
        cor34_normalizedBlockWave ε p =
      normΛ • cor34_normalizedBlockWave ε p := by
  have hmatrixC : (cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ) =
      (((-ε / 2 : ℝ) : ℂ) ^ n) •
        (transferBlock N (Real.sqrt (2 - 2 / ε)) n).map (algebraMap ℝ ℂ) := by
    rw [cor34_normalizedTransferBlock_eq_scaled_transferBlock ε hε,
      ← inv_pow, show (-2 / ε : ℝ)⁻¹ = -ε / 2 by field_simp [hε.ne]]
    ext x y; simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  have hwave : cor34_normalizedBlockWave (N := N) ε p =
      (((-ε / 2 : ℝ) : ℂ) ^ cor34_pairCount n) • BetheAnsatz.blockWave (N := N) (1 / ε) p := by
    funext x
    exact cor34_normalizedCoordinate_eq_scaled_coordinateWave ε p (BetheAnsatz.positions x) hε.ne
  rw [hmatrixC, hwave, hscale]
  exact cor34_final_scale_eigen_equation hraw

private theorem cor34_final_c_gt_two_and_anisotropy {ε : ℝ} (hε : ε < 0) (hInv : 1 / ε < -1) :
    2 < Real.sqrt (2 - 2 / ε) ∧ BetheAnsatz.anisotropy (Real.sqrt (2 - 2 / ε)) = 1 / ε := by
  have hcSq : (Real.sqrt (2 - 2 / ε)) ^ 2 = 2 - 2 / ε :=
    Real.sq_sqrt (by linarith [div_neg_of_pos_of_neg two_pos hε])
  have hparam : 4 < 2 - 2 / ε := by
    rw [show 2 / ε = 2 * (1 / ε) by ring]; linarith
  refine ⟨by rw [Real.lt_sqrt (by norm_num)]; linarith, ?_⟩
  unfold BetheAnsatz.anisotropy; rw [hcSq]; ring

theorem cor34_final_even_normalized_eigen {N n : ℕ} {ε : ℝ}
    (hε : ε < 0) (hInv : 1 / ε < -1)
    (p : Fin n → ℝ) (hp : p ∈ Bethe.S_n n) (hn : Even n)
    (hBE : Bethe.DiscreteBetheEquation (1 / ε) N n p) :
    (cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ) *ᵥ
        cor34_normalizedBlockWave ε p =
      cor34_normalizedRegularEigenvalue ε p • cor34_normalizedBlockWave ε p := by
  obtain ⟨hc, hAni⟩ := cor34_final_c_gt_two_and_anisotropy hε hInv
  exact cor34_final_normalized_eigen_of_raw hε p
    (cor34_final_even_block_eigen hc hAni p hp hn hBE)
    (cor34_final_normalizedRegularEigenvalue_scale hε p)

theorem cor34_final_odd_normalized_eigen {N n q : ℕ} {ε : ℝ}
    (hε : ε < 0) (hInv : 1 / ε < -1)
    (p : Fin n → ℝ) (hp : p ∈ Bethe.S_n n) (hnq : n + 1 = 2 * q)
    (hBE : Bethe.DiscreteBetheEquation (1 / ε) N n p) :
    (cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ) *ᵥ
        cor34_normalizedBlockWave ε p =
      cor34_normalizedZeroEigenvalue (N := N) ε p
          (⟨q - 1, by omega⟩ : Fin n) • cor34_normalizedBlockWave ε p := by
  obtain ⟨hc, hAni⟩ := cor34_final_c_gt_two_and_anisotropy hε hInv
  exact cor34_final_normalized_eigen_of_raw hε p
    (cor34_final_odd_block_eigen hc hAni p hp hnq hBE)
    (cor34_final_normalizedZeroEigenvalue_scale (⟨q - 1, by omega⟩ : Fin n) hInv hε p)

end PottsDiscontinuity.SixVertex
