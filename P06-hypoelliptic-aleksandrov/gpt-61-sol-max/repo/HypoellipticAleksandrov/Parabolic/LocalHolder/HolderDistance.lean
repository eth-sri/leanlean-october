module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.Geometry
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ForcedIterationGeometry

/-! # The literal parabolic distance and two-point cylinder geometry -/

 public section

namespace HypoellipticAleksandrov.Parabolic.LocalHolder

open KineticAleksandrov.LocalA

variable {N : ℕ}

variable (z z' : TimeVelocity N)

/-- The literal parabolic distance is nonnegative. -/
theorem parabolicDistance_nonneg   :
    0 ≤ parabolicDistance z z' :=
  add_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (PDE.vecEuclideanNorm_nonneg _)

/-- The time difference is bounded by the square of the parabolic distance. -/
theorem abs_time_sub_le_parabolicDistance_sq   :
    |z.1 - z'.1| ≤ parabolicDistance z z' ^ 2 := by



  unfold parabolicDistance
  rw [← Real.sqrt_eq_rpow]
  nlinarith only [(PDE.vecEuclideanNorm_nonneg (z.2 - z'.2)), (Real.sqrt_nonneg |z.1 - z'.1|), (Real.sq_sqrt (abs_nonneg (z.1 - z'.1)))]

/-- The velocity difference is bounded by the parabolic distance. -/
theorem velocity_sub_le_parabolicDistance   :
    PDE.vecEuclideanNorm (z.2 - z'.2) ≤ parabolicDistance z z' :=
  le_add_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _)

variable {z z' : TimeVelocity N}

/-- Distinct points have strictly positive parabolic distance. -/
theorem parabolicDistance_pos   (hne : z ≠ z') :
    0 < parabolicDistance z z' := by

  by_contra h

  have ht := abs_time_sub_le_parabolicDistance_sq z z'
  have hv := velocity_sub_le_parabolicDistance z z'
  rw [(le_antisymm (not_lt.mp h) (parabolicDistance_nonneg z z'))] at ht hv
  have ht0 : z.1 = z'.1 := sub_eq_zero.mp (abs_eq_zero.mp (by
    simp_all))
  have hv0  := sub_eq_zero.mp (PDE.vecEuclideanNorm_eq_zero_iff.mp
    (le_antisymm hv (PDE.vecEuclideanNorm_nonneg _)))
  exact hne (Prod.ext ht0 hv0)

/-- A positive future margin can always be chosen below the fixed top time zero. -/
theorem exists_pair_top
    (hz : z.1 < 0) (hz' : z'.1 < 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℝ, max z.1 z'.1 < T ∧ T < 0 ∧ T - max z.1 z'.1 ≤ δ ^ 2 := by
  let t := max z.1 z'.1
  have ht : t < 0 := max_lt hz hz'
  let e := min (δ ^ 2) (-t) / 2

  have heδ : e ≤ δ ^ 2 :=
    (div_le_self (le_of_lt (lt_min (sq_pos_of_pos hδ) (neg_pos.mpr ht)))
      (by norm_num)).trans (min_le_left _ _)
  have het : e < -t := by

    dsimp only [e]
    linarith only [(min_le_right (δ ^ 2) (-t)), ht]
  exact ⟨t + e, lt_add_of_pos_right t (half_pos (lt_min (sq_pos_of_pos hδ) (neg_pos.mpr ht))), by linarith only [het],
    by simpa only [t, add_sub_cancel_left] using heδ⟩

end HypoellipticAleksandrov.Parabolic.LocalHolder
