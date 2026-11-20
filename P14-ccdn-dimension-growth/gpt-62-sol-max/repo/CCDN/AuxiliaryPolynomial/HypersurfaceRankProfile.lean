/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Bounds

/-! Uniform bounds for the exact homogeneous hypersurface Hilbert rank.
The factorial leading coefficient is retained in both directions. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset

/-- The degree-`M` monomial count modulo a form of degree `d` in `n + 1` variables. -/
def hypersurfaceRank (n d M : ℕ) : ℕ := (n + M).choose M - (n + (M - d)).choose (M - d)

lemma hypersurfaceRank_add_kernel (n d M : ℕ) :
    hypersurfaceRank n d M + (n + (M - d)).choose (M - d) = (n + M).choose M := by
  apply Nat.sub_add_cancel
  rw [← Nat.choose_symm_add, ← Nat.choose_symm_add (a := n) (b := M)]
  exact Nat.choose_le_choose _ (by omega)

private lemma sum_shifted_choose_add (r k d : ℕ) :
    (∑ i ∈ range d, (r + 1 + k + i).choose r) + (r + 1 + k).choose (r + 1) =
      (r + 1 + k + d).choose (r + 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ]
    grind

section

variable {r d M : ℕ} (hdM : d ≤ M)
include r d M hdM

local notation "s₀" => hypersurfaceRank (r + 1) d M

/-- The exact rank is a sum of d adjacent binomial layers. -/
private theorem hypersurface_rank_eq_sum :
    s₀ = ∑ i ∈ range d, (r + 1 + (M - d) + i).choose r := by
  have hr := hypersurfaceRank_add_kernel (r + 1) d M
  have hh := sum_shifted_choose_add r (M - d) d
  rw [show r + 1 + (M - d) + d = r + 1 + M by omega] at hh
  rw [← Nat.choose_symm_add (a := r + 1) (b := M - d),
    ← Nat.choose_symm_add (a := r + 1) (b := M)] at hr
  omega

/-- The Hilbert function `s` of a degree-`d` hypersurface in `r + 2` homogeneous variables,
given by `s + C(r + 1 + (M - d), M - d) = C(r + 1 + M, M)`, satisfies
`d * C(r + (M - d), r) ≤ s ≤ d * C(r + M, r)`. -/
lemma hypersurface_rank_binomial_bounds :
    d * (r + (M - d)).choose r ≤ s₀ ∧ s₀ ≤ d * (r + M).choose r := by
  rw [hypersurface_rank_eq_sum hdM]
  constructor
  · calc
      _ = ∑ _i ∈ range d, (r + (M - d)).choose r := by simp
      _ ≤ _ := sum_le_sum fun i _ => Nat.choose_le_choose r (by omega)
  · calc
      _ ≤ ∑ _i ∈ range d, (r + M).choose r :=
        sum_le_sum fun i hi => Nat.choose_le_choose r (by grind)
      _ = _ := by simp

lemma hypersurface_rank_pos (hd : 0 < d) : 0 < s₀ :=
  (Nat.mul_pos hd (Nat.choose_pos (Nat.le_add_right _ _))).trans_le
    (hypersurface_rank_binomial_bounds hdM).1

/-- Uniform power bounds with exact leading coefficient d/r!.
The error is controlled by shifts of at most d and r in the degree M. -/
theorem hypersurface_rank_power_bounds :
    (d : ℝ) * ((M : ℝ) - d + 1) ^ r / (r.factorial : ℝ) ≤ s₀ ∧
      (s₀ : ℝ) ≤ (d : ℝ) * ((M : ℝ) + r) ^ r / (r.factorial : ℝ) := by
  obtain ⟨hlo, hhi⟩ := hypersurface_rank_binomial_bounds hdM
  have hloR : (d : ℝ) * ((r + (M - d)).choose r : ℝ) ≤ s₀ := by exact_mod_cast hlo
  have hhiR : (s₀ : ℝ) ≤ (d : ℝ) * ((r + M).choose r : ℝ) := by exact_mod_cast hhi
  have hl : ((M : ℝ) - d + 1) ^ r / (r.factorial : ℝ) ≤ (r + (M - d)).choose r := by
    have h := Nat.pow_le_choose (α := ℝ) r (r + (M - d))
    rw [show r + (M - d) + 1 - r = M - d + 1 by omega] at h
    simp_all
  have hu : ((r + M).choose r : ℝ) ≤ ((M : ℝ) + r) ^ r / (r.factorial : ℝ) := by
    grind [Nat.choose_le_pow_div]
  constructor
  · have h := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg d)
    grind
  · exact hhiR.trans
      (by simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg d))

end

end
end CCDN
