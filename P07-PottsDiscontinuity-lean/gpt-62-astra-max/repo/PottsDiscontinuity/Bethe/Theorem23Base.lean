module

public import PottsDiscontinuity.Bethe.Theorem23Inverse
public import PottsDiscontinuity.Bethe.Theorem23StrictGaps

/-! # The unique base fiber and its cyclic gap estimates -/

@[expose] public section

open Set
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

noncomputable def discreteBaseCoordinates (N n : ℕ) : Fin (n / 2) → ℝ :=
  fun i => discreteBaseSolution N n (discreteHalfIndex i)

section
variable {N n : ℕ} (hN : 0 < N) (hs : 2 * n ≤ N)
include hN hs

theorem discreteCoordinateResidualInv_base_zero :
    discreteCoordinateResidualInv 0 N n (discreteBaseCoordinates N n) = 0 := by
  have hNc : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hlift : discreteSymLift n (discreteBaseCoordinates N n) = discreteBaseSolution N n :=
    discreteSymLift_coordinates _ (discreteBaseSolution_mem_S_n hN hs).2.2
  funext i
  have heq := (discreteBaseSolution_solves_at_infinity hN hs) (discreteHalfIndex i)
  simp only [discreteCoordinateResidualInv, discreteBetheMapInv, thetaInv_zero, hlift]
  change discreteBaseSolution N n (discreteHalfIndex i) - _ = 0
  grind

/-- The base root is unique among all symmetric coordinate vectors, not merely
among the admissible configurations. -/
theorem discreteCoordinateResidualInv_base_unique :
    ∃! q, discreteCoordinateResidualInv 0 N n q = 0 := by
  refine ⟨discreteBaseCoordinates N n, discreteCoordinateResidualInv_base_zero hN hs,
    fun q hq => ?_⟩
  have hnN : (n : ℝ) < N := by exact_mod_cast (show n < N by omega)
  have ha := sub_pos.mpr ((div_lt_one (by exact_mod_cast hN)).2 hnN)
  have hb := discreteCoordinateResidualInv_base_zero hN hs
  dsimp only at hq
  rw [discreteCoordinateResidualInv_zero] at hq hb
  funext i
  nlinarith only [(congrFun hq i), (congrFun hb i), ha]

end

/-- Exact cyclic gaps of the explicit base solution. -/
theorem discreteBaseSolution_cyclic_gap {N k : ℕ}
    (hs : 2 * (k + 1) ≤ N) (j : Fin (k + 2)) :
    rootPartitionPoint (discreteBaseSolution N (k + 1)) (by omega) j.succ -
      rootPartitionPoint (discreteBaseSolution N (k + 1)) (by omega) j.castSucc =
      2 * Real.pi * rootGapMultiplicity N (k + 1) j / ((N : ℝ) - (k + 1 : ℕ)) := by
  have hden : ((N - (k + 1) : ℕ) : ℝ) = (N : ℝ) - (k + 1 : ℕ) :=
    Nat.cast_sub (by omega)
  have hpos : 0 < (N : ℝ) - (k + 1 : ℕ) := by
    apply sub_pos.mpr
    exact_mod_cast (show k + 1 < N by omega)
  have hmass : ((N + 1 - 2 * (k + 1) : ℕ) : ℝ) =
      (N : ℝ) + 1 - 2 * ((k : ℝ) + 1) := by
    rw [Nat.cast_sub (by omega : 2 * (k + 1) ≤ N + 1)]
    push_cast
    ring
  by_cases hj0 : j.val = 0
  · have hj : j = 0 := Fin.ext hj0
    subst j
    have ha : rootPartitionPoint (discreteBaseSolution N (k + 1))
        (by omega) (0 : Fin (k + 2)).castSucc =
          discreteBaseSolution N (k + 1) (Fin.last k) - 2 * Real.pi := by
      rfl
    have hb : rootPartitionPoint (discreteBaseSolution N (k + 1))
        (by omega) (0 : Fin (k + 2)).succ = discreteBaseSolution N (k + 1) 0 := by
      congr 1
    rw [ha, hb]
    simp only [rootGapMultiplicity, Fin.val_zero, true_or, ite_true,
      discreteBaseSolution, discreteBetheIndex, Fin.val_last, hden, hmass]
    field_simp [hpos.ne']
    push_cast
    ring
  · by_cases hjlast : j.val = k + 1
    · have hj : j = Fin.last (k + 1) := Fin.ext hjlast
      subst j
      have ha : rootPartitionPoint (discreteBaseSolution N (k + 1))
          (by omega) (Fin.last (k + 1)).castSucc = discreteBaseSolution N (k + 1) (Fin.last k) := by
        convert rootPartitionPoint_root (discreteBaseSolution N (k + 1)) (by omega)
          (Fin.last k) using 1
        congr 1
      have hb : rootPartitionPoint (discreteBaseSolution N (k + 1))
          (by omega) (Fin.last (k + 1)).succ = discreteBaseSolution N (k + 1) 0 + 2 * Real.pi := by
        convert rootPartitionPoint_end (discreteBaseSolution N (k + 1)) (by omega) using 1 <;> congr 1
      rw [ha, hb]
      simp only [rootGapMultiplicity, Fin.val_last, or_true, ite_true,
        discreteBaseSolution, discreteBetheIndex, Fin.val_zero, hden, hmass]
      field_simp [hpos.ne']
      push_cast
      ring
    · let lo : Fin (k + 1) := ⟨j.val - 1, by omega⟩
      let hi : Fin (k + 1) := ⟨j.val, by omega⟩
      have ha : rootPartitionPoint (discreteBaseSolution N (k + 1))
          (by omega) j.castSucc = discreteBaseSolution N (k + 1) lo := by
        convert rootPartitionPoint_root (discreteBaseSolution N (k + 1)) (by omega) lo using 1
        congr 1
        grind
      have hb : rootPartitionPoint (discreteBaseSolution N (k + 1))
          (by omega) j.succ = discreteBaseSolution N (k + 1) hi := by
        convert rootPartitionPoint_root (discreteBaseSolution N (k + 1)) (by omega) hi using 1
        congr 1
      rw [ha, hb]
      simp only [rootGapMultiplicity, ite_eq_right (not_or.mpr ⟨hj0, hjlast⟩),
        discreteBaseSolution, discreteBetheIndex, lo, hi, hden]
      rw [Nat.cast_sub (by omega : 1 ≤ j.val)]
      ring

/-- The explicit base configuration is strictly inside the gap region used by
the bootstrap. -/
theorem discreteBaseCoordinates_strict_gaps {N k r : ℕ} (hN : 0 < N)
    (hs : 2 * (k + 1) ≤ N) (hcount : N = 2 * ((k + 1) + r))
    {c D : ℝ} (hc : c ≤ Real.pi) (hD : 8 * Real.pi * (2 * r + 1) < D)
    (j : Fin (k + 2)) :
    rootPartitionPoint (discreteSymLift (k + 1) (discreteBaseCoordinates N (k + 1)))
      (by omega) j.succ -
      rootPartitionPoint (discreteSymLift (k + 1) (discreteBaseCoordinates N (k + 1)))
      (by omega) j.castSucc ∈ Ioo (c / N) (D / N) := by
  have hlift : discreteSymLift _ (discreteBaseCoordinates N (k + 1)) =
      discreteBaseSolution N _ := discreteSymLift_coordinates _ (discreteBaseSolution_mem_S_n hN hs).2.2
  rw [hlift, discreteBaseSolution_cyclic_gap hs]
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  have hnN : ↑(k + 1) < (N : ℝ) := by exact_mod_cast (by omega)
  have hden : 0 < (N : ℝ) - ↑(k + 1) := by linarith
  have hhalf : N ≤ 2 * ((N : ℝ) - ↑(k + 1)) := by
    have hh : 2 * ((k : ℝ) + 1) ≤ N := by exact_mod_cast hs
    push_cast
    linarith
  have hdenN : (N : ℝ) - ↑(k + 1) ≤ N := by
    linarith
  have hm := one_le_rootGapMultiplicity hs j
  constructor
  · exact (div_lt_div_of_pos_right (by linarith [Real.pi_pos] : c < 2 * Real.pi) hNc).trans_le (by
      apply (div_le_div_iff₀ hNc hden).2
      have h₁ := mul_le_mul_of_nonneg_left hdenN (by positivity : 0 ≤ 2 * Real.pi)
      have h₂ := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2 * Real.pi * (N : ℝ))
      linarith)
  · have hu : 2 * Real.pi * rootGapMultiplicity N _ j /
        (N - ↑(k + 1)) ≤ 4 * Real.pi * (2 * r + 1) / N := by
      apply (div_le_div_iff₀ hden hNc).2
      have h₁ := mul_le_mul_of_nonneg_left (rootGapMultiplicity_le_offset hs hcount j) (by positivity : 0 ≤ 2 * Real.pi * N)
      have h₂ := mul_le_mul_of_nonneg_left hhalf
        (by positivity : 0 ≤ 2 * Real.pi * (2 * r + 1))
      linarith
    have hD' : 4 * Real.pi * (2 * r + 1) < D := by
      have hpi : 0 < Real.pi * (2 * r + 1) := by positivity
      linarith
    exact hu.trans_lt (div_lt_div_of_pos_right hD' hNc)

end PottsDiscontinuity.Bethe
