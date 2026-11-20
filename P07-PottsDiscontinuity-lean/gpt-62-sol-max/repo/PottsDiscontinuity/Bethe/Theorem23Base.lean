module

public import PottsDiscontinuity.Bethe.Theorem23Inverse
public import PottsDiscontinuity.Bethe.Theorem23StrictGaps

/-! # The unique base fiber and its cyclic gap estimates -/

@[expose] public section

open Set
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

noncomputable def discreteBaseCoordinates (N n : ℕ) : Fin (n / 2) → ℝ :=
  fun i => discreteBaseSolution N n (discreteHalfIndex n i)

theorem discreteCoordinateResidualInv_base_zero {N n : ℕ} (hN : 0 < N)
    (hs : 2 * n ≤ N) :
    discreteCoordinateResidualInv 0 N n (discreteBaseCoordinates N n) = 0 := by
  have hp := discreteBaseSolution_mem_S_n hN hs
  have hBE := discreteBaseSolution_solves_at_infinity hN hs
  have hNc : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hlift : discreteSymLift n (discreteBaseCoordinates N n) = discreteBaseSolution N n :=
    discreteSymLift_coordinates _ hp.2.2
  funext i
  have heq := hBE (discreteHalfIndex n i)
  simp only [discreteCoordinateResidualInv, discreteBetheMapInv, thetaInv_zero, hlift]
  change discreteBaseSolution N n (discreteHalfIndex n i) - _ = 0
  field_simp [hNc]
  nlinarith only [heq]

/-- The base root is unique among all symmetric coordinate vectors, not merely
among the admissible configurations. -/
theorem discreteCoordinateResidualInv_base_unique {N n : ℕ} (hN : 0 < N)
    (hs : 2 * n ≤ N) :
    ∃! q : Fin (n / 2) → ℝ, discreteCoordinateResidualInv 0 N n q = 0 := by
  refine ⟨discreteBaseCoordinates N n, discreteCoordinateResidualInv_base_zero hN hs,
    fun q hq => ?_⟩
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  have hnN : (n : ℝ) < N := by norm_cast at *; omega
  have ha := sub_pos.mpr ((div_lt_one hNc).2 hnN)
  have hb := discreteCoordinateResidualInv_base_zero hN hs
  dsimp only at hq
  rw [discreteCoordinateResidualInv_zero] at hq hb
  funext i
  have hqi := congrFun hq i
  have hbi := congrFun hb i
  nlinarith only [hqi, hbi, ha]

/-- Exact cyclic gaps of the explicit base solution. -/
theorem discreteBaseSolution_cyclic_gap {N k : ℕ} (_hN : 0 < N)
    (hs : 2 * (k + 1) ≤ N) (j : Fin (k + 2)) :
    rootPartitionPoint (k + 1) (discreteBaseSolution N (k + 1)) (by omega) j.succ -
      rootPartitionPoint (k + 1) (discreteBaseSolution N (k + 1)) (by omega) j.castSucc =
      2 * Real.pi * rootGapMultiplicity N (k + 1) j / ((N : ℝ) - (k + 1 : ℕ)) := by
  have hden : ((N - (k + 1) : ℕ) : ℝ) = (N : ℝ) - (k + 1 : ℕ) := Nat.cast_sub (by omega)
  have hn : (k + 1 : ℕ) < (N : ℝ) := by exact_mod_cast (show k + 1 < N by omega)
  have h := rootPartitionPoint_increment hs (p := discreteBaseSolution N (k + 1)) id
    (2 * Real.pi / ((N : ℝ) - (k + 1 : ℕ))) (fun i => by simp [discreteBaseSolution, hden]; ring)
    (fun x => by simp only [id_eq, mul_div_cancel₀ _ (sub_pos.mpr hn).ne']) j
  simpa [← mul_div_assoc, mul_comm _ (2 * Real.pi)] using h

/-- The explicit base configuration is strictly inside the gap region used by
the bootstrap. -/
theorem discreteBaseCoordinates_strict_gaps {N k r : ℕ} (hN : 0 < N)
    (hs : 2 * (k + 1) ≤ N) (hcount : N = 2 * ((k + 1) + r))
    {c D : ℝ} (hc : c ≤ Real.pi) (hD : 8 * Real.pi * (2 * r + 1 : ℝ) < D)
    (j : Fin (k + 2)) :
    rootPartitionPoint (k + 1) (discreteSymLift (k + 1) (discreteBaseCoordinates N (k + 1)))
      (by omega) j.succ -
      rootPartitionPoint (k + 1) (discreteSymLift (k + 1) (discreteBaseCoordinates N (k + 1)))
      (by omega) j.castSucc ∈ Ioo (c / (N : ℝ)) (D / (N : ℝ)) := by
  have hp := discreteBaseSolution_mem_S_n hN hs
  have hlift : discreteSymLift (k + 1) (discreteBaseCoordinates N (k + 1)) =
      discreteBaseSolution N (k + 1) := discreteSymLift_coordinates _ hp.2.2
  rw [hlift, discreteBaseSolution_cyclic_gap hN hs]
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  have hnat : k + 1 < N := by omega
  have hnN : (k + 1 : ℕ) < (N : ℝ) := by exact_mod_cast hnat
  have hden : 0 < (N : ℝ) - (k + 1 : ℕ) := by linarith
  have hhalf : (N : ℝ) ≤ 2 * ((N : ℝ) - (k + 1 : ℕ)) := by
    have hh : 2 * ((k : ℝ) + 1) ≤ N := by exact_mod_cast hs
    push_cast
    linarith
  have hdenN : (N : ℝ) - (k + 1 : ℕ) ≤ N := by
    linarith
  have hm := one_le_rootGapMultiplicity hs j
  have hmcap := rootGapMultiplicity_le_offset hs hcount j
  constructor
  · have hlo : 2 * Real.pi / (N : ℝ) ≤
        2 * Real.pi * rootGapMultiplicity N (k + 1) j / ((N : ℝ) - (k + 1 : ℕ)) := by
      apply (div_le_div_iff₀ hNc hden).2
      have h₁ := mul_le_mul_of_nonneg_left hdenN (by positivity : 0 ≤ 2 * Real.pi)
      have h₂ := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2 * Real.pi * (N : ℝ))
      nlinarith only [h₁, h₂]
    exact (div_lt_div_of_pos_right (by linarith [Real.pi_pos] : c < 2 * Real.pi) hNc).trans_le hlo
  · have hu : 2 * Real.pi * rootGapMultiplicity N (k + 1) j /
        ((N : ℝ) - (k + 1 : ℕ)) ≤ 4 * Real.pi * (2 * r + 1 : ℝ) / (N : ℝ) := by
      apply (div_le_div_iff₀ hden hNc).2
      have h₁ := mul_le_mul_of_nonneg_left hmcap (by positivity : 0 ≤ 2 * Real.pi * (N : ℝ))
      have h₂ := mul_le_mul_of_nonneg_left hhalf
        (by positivity : 0 ≤ 2 * Real.pi * (2 * r + 1 : ℝ))
      nlinarith only [h₁, h₂]
    have hD' : 4 * Real.pi * (2 * r + 1 : ℝ) < D := by
      have hpi : 0 < Real.pi * (2 * r + 1 : ℝ) := by positivity
      linarith
    exact hu.trans_lt (div_lt_div_of_pos_right hD' hNc)

end PottsDiscontinuity.Bethe
