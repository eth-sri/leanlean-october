module
public import Mathlib

public import PottsDiscontinuity.Bethe.Theorem23Inverse
public import PottsDiscontinuity.Bethe.Theorem23StrictGaps

/-! # The unique base fiber and its cyclic gap estimates -/

@[expose] public section

open Set


namespace PottsDiscontinuity.Bethe

noncomputable def discreteBaseCoordinates (N n : ℕ) : Fin (n / 2) → ℝ :=
  fun i => discreteBaseSolution N n (discreteHalfIndex n i)

section

variable {N n : ℕ} (hN : 0 < N) (hs : 2 * n ≤ N)
include hN hs

theorem discreteCoordinateResidualInv_base_zero  :
    discreteCoordinateResidualInv 0 N n (discreteBaseCoordinates N n) = 0 := by
  
  
  
  have hlift : discreteSymLift n (discreteBaseCoordinates N n) = discreteBaseSolution N n :=
    discreteSymLift_coordinates _ (discreteBaseSolution_mem_S_n hN hs).2.2
  funext i
  
  simp only [discreteCoordinateResidualInv, discreteBetheMapInv, thetaInv_zero, hlift]
  change discreteBaseSolution N n (discreteHalfIndex n i) - _ = 0
  field_simp 
  nlinarith only [ (discreteBaseSolution_solves_at_infinity hN hs) (discreteHalfIndex n i) ]

/-- The base root is unique among all symmetric coordinate vectors, not merely
among the admissible configurations. -/
theorem discreteCoordinateResidualInv_base_unique  :
    ∃! q : Fin (n / 2) → ℝ, discreteCoordinateResidualInv 0 N n q = 0 := by
  refine ⟨discreteBaseCoordinates N n, discreteCoordinateResidualInv_base_zero hN hs,
    fun q hq => ?_⟩
  
  have hnN : (n : ℝ) < N := by exact_mod_cast  by omega 
  
  have hb := discreteCoordinateResidualInv_base_zero hN hs
  dsimp only at hq
  rw [discreteCoordinateResidualInv_zero] at hq hb
  funext i
  
  
  
  nlinarith only [(congrFun hq i), (congrFun hb i),  sub_pos.mpr ((div_lt_one (by exact_mod_cast hN)).2 hnN) ]

end

/-- Exact cyclic gaps of the explicit base solution. -/
theorem discreteBaseSolution_cyclic_gap {N k : ℕ} (_hN : 0 < N)
    (hs : 2 * (k + 1) ≤ N) (j : Fin (k + 2)) :
    rootPartitionPoint (k + 1) (discreteBaseSolution N (k + 1)) (by omega) j.succ -
      rootPartitionPoint (k + 1) (discreteBaseSolution N (k + 1)) (by omega) j.castSucc =
      2 * Real.pi * rootGapMultiplicity N (k + 1) hs j / ((N : ℝ) - (k + 1 : ℕ)) := by
  have hden :  (N - (k + 1) : ℕ)  = (N : ℝ) - (k + 1 : ℕ) :=
    Nat.cast_sub (by omega)
  have hpos : 0 < (N : ℝ) - (k + 1 : ℕ) := by
    apply sub_pos.mpr
    exact_mod_cast  by omega 
  have hmass :  (N + 1 - 2 * (k + 1) : ℕ)  =
       N  + 1 - 2 * ((k : ℝ) + 1) := by
    rw [Nat.cast_sub (by omega )]
    push_cast
    ring
  by_cases hj0 : j.val = 0
  · have hj : j = 0 := Fin.ext hj0
    subst j
    have ha : rootPartitionPoint (k + 1) (discreteBaseSolution N (k + 1))
        (by omega) (0 : Fin (k + 2)).castSucc =
          discreteBaseSolution N (k + 1) (Fin.last k) - 2 * Real.pi := rfl
    have hb : rootPartitionPoint (k + 1) (discreteBaseSolution N (k + 1))
        (by omega) (0 : Fin (k + 2)).succ = discreteBaseSolution N (k + 1) 0 := rfl
    rw [ha, hb]
    simp only [rootGapMultiplicity, Fin.val_zero, true_or, discreteBaseSolution, discreteBetheIndex, hden, hmass]
    field_simp 
    push_cast
    ring
  · by_cases hjlast : j.val = k + 1
    · grind [rootPartitionPoint, discreteBaseSolution, rootGapMultiplicity, discreteBetheIndex]
    · let lo : Fin (k + 1) := ⟨j.val - 1, by omega⟩
      let hi : Fin (k + 1) := ⟨j.val, by omega⟩
      
      have hb : rootPartitionPoint (k + 1) (discreteBaseSolution N (k + 1))
          (by omega) j.succ = discreteBaseSolution N (k + 1) hi := by
        convert rootPartitionPoint_root (discreteBaseSolution N (k + 1)) (by omega) hi using 1
        congr 1
      rw [(by
             convert rootPartitionPoint_root (discreteBaseSolution N (k + 1)) (by omega) lo using 1
             congr 1
             grind : rootPartitionPoint (k + 1) (discreteBaseSolution N (k + 1))
          (by omega) j.castSucc = discreteBaseSolution N (k + 1) lo), hb]
      simp only [rootGapMultiplicity, ite_eq_right (not_or.mpr ⟨hj0, hjlast⟩), discreteBaseSolution, discreteBetheIndex, hden]
      rw [Nat.cast_sub (by omega )]
      
      ring

/-- The explicit base configuration is strictly inside the gap region used by
the bootstrap. -/
theorem discreteBaseCoordinates_strict_gaps {N k r : ℕ} (hN : 0 < N)
    (hs : 2 * (k + 1) ≤ N) (hcount : N = 2 * ( k + 1  + r))
    {c D : ℝ} (hc : c ≤ Real.pi) (hD : 8 * Real.pi * (2 * r + 1 : ℝ) < D)
    (j : Fin (k + 2)) :
    rootPartitionPoint (k + 1) (discreteSymLift (k + 1) (discreteBaseCoordinates N (k + 1)))
      (by omega) j.succ -
      rootPartitionPoint (k + 1) (discreteSymLift (k + 1) (discreteBaseCoordinates N (k + 1)))
      (by omega) j.castSucc ∈ Ioo (c / (N : ℝ)) (D / (N : ℝ)) := by
  
  have hlift : discreteSymLift (k + 1) (discreteBaseCoordinates N (k + 1)) =
      discreteBaseSolution N (k + 1) := discreteSymLift_coordinates _ (discreteBaseSolution_mem_S_n hN hs).2.2
  rw [hlift, discreteBaseSolution_cyclic_gap hN hs]
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  
  have hnN : (k + 1 : ℕ) < (N : ℝ) := by exact_mod_cast  by omega 
  have hden : 0 < (N : ℝ) - (k + 1 : ℕ) := by linarith
  have hhalf :  N  ≤ 2 * ((N : ℝ) - (k + 1 : ℕ)) := by
    simp_all <;> nlinarith
  have hdenN : (N : ℝ) - (k + 1 ) ≤ N := by
    linarith
  have hm := one_le_rootGapMultiplicity hs j
  
  constructor
  · 
    exact (div_lt_div_of_pos_right (by linarith [Real.pi_pos] : c < 2 * Real.pi) hNc).trans_le (by
                                                                                                  bound)
  · have hu : 2 * Real.pi * rootGapMultiplicity N (k + 1) hs j /
        ( N  - (k + 1 : ℕ)) ≤ 4 * Real.pi * (2 * r + 1 ) /  N  := by
      apply (div_le_div_iff₀ hden hNc).2
      have h₁ := mul_le_mul_of_nonneg_left (rootGapMultiplicity_le_offset hs hcount j) (by positivity : 0 ≤ 2 * Real.pi * (N : ℝ))
      have h₂ := mul_le_mul_of_nonneg_left hhalf
        (by positivity : 0 ≤ 2 * Real.pi * (2 * r + 1 : ℝ))
      nlinarith only [h₁, h₂]
    
    exact hu.trans_lt (div_lt_div_of_pos_right (by
                                                  have hpi : 0 < Real.pi * (2 * r + 1 ) := by positivity
                                                  linarith) hNc)

end PottsDiscontinuity.Bethe
