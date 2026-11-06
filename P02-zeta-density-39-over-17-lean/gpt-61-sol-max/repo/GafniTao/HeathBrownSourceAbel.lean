module
public import GafniTao.HeathBrownAbelWeight

@[expose] public section

/-!
# Finite Abel summation on the source interval

Unlike the reusable frozen helper whose terminal weight lies one index beyond
its range, this identity is written on `1 ≤ h ≤ H`.  Consequently all
variation terms are genuine source edges and no `H+1` regularity is assumed.
-/

open Finset
open scoped BigOperators

namespace GafniTao



section
variable (w a : ℕ → ℂ) {H : ℕ} (hH : 1 ≤ H)
include w a H hH

theorem heathBrown_source_abel_identity
     :
    (∑ h ∈ Finset.Icc 1 H, w h * a h) =
      w H * (∑ h ∈ Finset.Icc 1 H, a h) +
        ∑ j ∈ Finset.Ico 1 H,
          (w j - w (j + 1)) * (∑ h ∈ Finset.Icc 1 j, a h) := by
  induction H with
  | zero => omega
  | succ H ih =>
      by_cases hHzero : H = 0
      · subst H
        simp
      · have hHpos : 1 ≤ H := Nat.one_le_iff_ne_zero.mpr hHzero
        have hih := ih hHpos
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ H + 1)]
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ H + 1)]
        rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ H)]
        rw [hih]
        ring

/-- Partial-sum form of finite Abel summation.  Each edge keeps its own
partial sum, which is essential when those partial sums are averaged over
coefficient cells. -/
theorem heathBrown_norm_source_weighted_le_partial
     (C : ℝ)
    (hweight : ‖w H‖ ≤ 1)
    (hedge : ∀ j ∈ Finset.Ico 1 H, ‖w (j + 1) - w j‖ ≤ C) :
    ‖∑ h ∈ Finset.Icc 1 H, w h * a h‖ ≤
      ‖∑ h ∈ Finset.Icc 1 H, a h‖ +
        C * ∑ j ∈ Finset.Ico 1 H,
          ‖∑ h ∈ Finset.Icc 1 j, a h‖ := by
  rw [heathBrown_source_abel_identity w a hH]
  calc
    _ ≤ ‖w H * (∑ h ∈ Finset.Icc 1 H, a h)‖ +
        ‖∑ j ∈ Finset.Ico 1 H,
          (w j - w (j + 1)) * (∑ h ∈ Finset.Icc 1 j, a h)‖ :=
      norm_add_le _ _
    _ ≤ ‖∑ h ∈ Finset.Icc 1 H, a h‖ +
        ∑ j ∈ Finset.Ico 1 H, C * ‖∑ h ∈ Finset.Icc 1 j, a h‖ := by
      apply add_le_add
      · rw [norm_mul]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hweight (norm_nonneg _)
      · calc
          _ ≤ ∑ j ∈ Finset.Ico 1 H,
              ‖(w j - w (j + 1)) *
                (∑ h ∈ Finset.Icc 1 j, a h)‖ := norm_sum_le _ _
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro j hj
            rw [norm_mul, norm_sub_rev]
            exact mul_le_mul_of_nonneg_right (hedge j hj) (norm_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]
end





