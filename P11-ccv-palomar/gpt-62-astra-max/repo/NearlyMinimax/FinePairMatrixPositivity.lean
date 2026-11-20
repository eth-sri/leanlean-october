module

public import NearlyMinimax.FinePairResponseGeometry
public import NearlyMinimax.CardinalCoefficientBounds


@[expose] public section

/-! Nondegeneracy of the genuine fine-pair response matrices. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem spatial_matrix_l1_eq_zero_iff {d F : ℕ}
    (A : HighFrameIndex d F → HighFrameVector d F) :
    spatialMatrixL1 A = 0 ↔ ∀ β β', A β β' = 0 := by
  constructor
  · intro h β β'
    have hentry : |A β β'| ≤ spatialMatrixL1 A := by
      calc
        _ ≤ _ := Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ β')
        _ ≤ _ := Finset.single_le_sum (f := fun β => ∑ γ, |A β γ|)
            (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
            (Finset.mem_univ β)
    grind
  · intro h
    simp [spatialMatrixL1, h]

variable (d F : ℕ)

theorem finePairUnitMatrix_l1_pos :
    0 < spatialMatrixL1 (finePairUnitMatrix d F) := by
  apply lt_of_le_of_ne (spatial_matrix_l1_nonnegative _) ?_
  intro he
  have hk := finePairUnitMatrix_kernel (d := d) (F := F)
    (n := 1) (fun _ => 0) 0 0
  simp only [spatialFrameCovariance, ((spatial_matrix_l1_eq_zero_iff _).mp he.symm), mul_zero, Finset.sum_const_zero] at hk
  norm_num at hk

theorem finePairDistanceMatrix_l1_pos [NeZero d] (hF : 3 ≤ F) :
    0 < spatialMatrixL1 (finePairDistanceMatrix d F) := by
  apply lt_of_le_of_ne (spatial_matrix_l1_nonnegative _) ?_
  intro he
  let U : DesignSample d 2 := fun i _ => if i = 0 then 0 else 1
  have hk := finePairDistanceMatrix_kernel hF U 0 1
  simp only [spatialFrameCovariance, ((spatial_matrix_l1_eq_zero_iff _).mp he.symm), mul_zero, Finset.sum_const_zero] at hk
  have heU : spatialSquaredDistance (U 0) (U 1) = d := by simp [U, spatialSquaredDistance]
  rw [heU] at hk
  exact NeZero.ne d (Nat.cast_eq_zero.mp (neg_eq_zero.mp hk.symm))

end NearlyMinimax
