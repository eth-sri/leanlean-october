/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import CCDN.AuxiliaryPolynomial.HypersurfaceRankProfile
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! A lower bound on the kernel-to-rank ratio, by adjacent binomial layers. -/

@[expose] public section
namespace CCDN
noncomputable section

lemma hypersurface_kernel_ratio_lower {r d M : ℕ} (hdM : d ≤ M) (hd : 0 < d) :
    let s := hypersurfaceRank (r + 1) d M
    (M : ℝ) - d * (r + 1 : ℝ) ≤
      (d : ℝ) * (r + 1 : ℝ) * ((r + 1 + (M - d)).choose (M - d) : ℝ) / s := by
  intro s
  have hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M :=
    hypersurfaceRank_add_kernel _ _ _
  have hs : 0 < s := hypersurface_rank_pos hdM hd
  have h := Nat.add_one_mul_choose_eq (r + M) r
  rw [show r + M + 1 = r + 1 + M by omega, Nat.choose_symm_add (a := r + 1), ← hr] at h
  have hh : s ≤ d * (r + M).choose r := (hypersurface_rank_binomial_bounds hdM).2
  have hle := Nat.mul_le_mul_left (r + 1 + M) hh
  rw [mul_left_comm, h] at hle
  apply (le_div_iff₀ (by exact_mod_cast hs)).mpr
  have hle' : ((r : ℝ) + 1 + M) * s ≤
      (d : ℝ) * ((s : ℝ) + ((r + 1 + (M - d)).choose (M - d) : ℝ)) * (r + 1 : ℝ) := by
    rw [mul_assoc]
    exact_mod_cast hle
  nlinarith only [hle', show 0 ≤ ((r : ℝ) + 1) * s by positivity]

end
end CCDN
