module
public import Mathlib

public import PottsDiscontinuity.Bethe.Theorem23Diagonal
public import PottsDiscontinuity.Bethe.Theorem23Rows

/-! # Actual diagonal dominance from a uniform mesh -/

@[expose] public section




namespace PottsDiscontinuity.Bethe

section

variable {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) (D : ℝ) (hD : 0 ≤ D)
include hΔ₀ hD

/-- Every Bethe solution with the specified uniform mesh has a strictly
row-diagonally-dominant rescaled Jacobian once `N` is sufficiently large. -/
theorem exists_uniform_rescaled_diagonal_dominance  :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ Δ ≤ Δ₀, ∀ (N k : ℕ), N₀ ≤ N →
      2 * (k + 1) ≤ N → ∀ (p : Fin (k + 1) → ℝ), p ∈ S_n (k + 1) →
      DiscreteBetheEquation Δ N (k + 1) p →
      (∀ j : Fin (k + 2), rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ D / (N : ℝ)) →
      ∀ i : Fin ((k + 1) / 2),
        ∑ j ∈ Finset.univ.erase i, |discreteBetheMatrixATilde Δ N (k + 1) p i j| <
          |discreteBetheMatrixATilde Δ N (k + 1) p i i| := by
  obtain ⟨Cdiag, hCdiag, hdiag⟩ := exists_uniform_rescaled_diagonal_estimate hΔ₀
  obtain ⟨Crow, hCrow, hrow⟩ := exists_uniform_rescaled_row_cyclic_estimate hΔ₀
  let b₀ := 4 * Real.arctan (1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1)))
  
  let E := Cdiag * (D ^ 2 + D) + Crow * D
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max 0 (E / (2 * Real.pi - b₀)))
  
  have hposNat : 0 < N₀ := by exact_mod_cast  (le_max_left _ _).trans_lt hN₀ 
  refine ⟨N₀, hposNat, fun Δ hΔ N k hlarge hs p hp hBE hmesh i => ?_⟩
  have hN  := lt_of_lt_of_le hposNat hlarge
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  have hcast : (N₀ : ℝ) ≤ N := by exact_mod_cast hlarge
  
  have hE : E /  N  < 2 * Real.pi - b₀ := by
    apply (div_lt_iff₀ hNc).2
    have ht := (div_lt_iff₀ (sub_pos.mpr  (discreteBetheG_endpoint_bound hΔ₀ le_rfl
                                               ⟨le_rfl, by linarith [Real.pi_pos]⟩ ).2 )).mp (((le_max_right _ _).trans_lt hN₀).trans_le hcast)
    nlinarith only [ht]
  
  
  
  
  
  
  have hrupper := (abs_le.mp (hrow Δ hΔ N k hN p hp (D /  N ) (div_nonneg hD hNc.le) hmesh i)).2
  
  rw [add_div] at hE
  
  have hmul : Crow * (D /  N ) = Crow * D /  N  := by ring
  rw [hmul] at hrupper
  linarith only [hE,  (abs_le.mp (hdiag Δ hΔ N (k + 1) hN hs p hp hBE D hD
                                                    (discreteHalf_gap_le_of_cyclic_mesh (by omega) p hmesh) i)).1 , hrupper, ((discreteBetheG_endpoint_bound hΔ₀ hΔ  ⟨(hp.1 _).1.le, (discreteS_n_half_coord_neg hp i).le⟩ ).1),  le_abs_self (discreteBetheMatrixATilde Δ N (k + 1) p i i) ]

/-- The symmetric-coordinate Jacobian itself is nonsingular. -/
theorem exists_uniform_Bethe_matrix_nonsingular  :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ Δ ≤ Δ₀, ∀ (N k : ℕ), N₀ ≤ N →
      2 * (k + 1) ≤ N → ∀ (p : Fin (k + 1) → ℝ), p ∈ S_n (k + 1) →
      DiscreteBetheEquation Δ N (k + 1) p →
      (∀ j : Fin (k + 2), rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ D / (N : ℝ)) →
      (discreteBetheMatrixA Δ N (k + 1) p).det ≠ 0 := by
  obtain ⟨N₀, hN₀, hdom⟩ := exists_uniform_rescaled_diagonal_dominance hΔ₀ D hD
  refine ⟨N₀, hN₀, fun Δ hΔ N k hlarge hs p hp hBE hmesh => ?_⟩
  have hdet := discrete_strict_row_diagonal_dominance_invertible
    (discreteBetheMatrixATilde Δ N (k + 1) p)
    (hdom Δ hΔ N k hlarge hs p hp hBE hmesh)
  rw [discreteBetheMatrixATilde, Matrix.det_mul] at hdet
  exact (mul_ne_zero_iff.mp hdet).1

end

end PottsDiscontinuity.Bethe
