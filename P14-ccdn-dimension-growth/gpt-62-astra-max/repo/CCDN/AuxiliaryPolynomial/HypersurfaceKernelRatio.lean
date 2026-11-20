/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic
import CCDN.AuxiliaryPolynomial.HypersurfaceRankProfile
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The homogeneous kernel-to-rank ratio differs from its leading term by
at most 1/M. Exact binomial identities avoid a formal asymptotic expansion. -/

@[expose] public section
namespace CCDN
noncomputable section

private lemma shifted_choose_successor_identity (r k : ℕ) :
    (r + k + 1) * (r + k).choose r = (r + 1 + k).choose (r + 1) * (r + 1) := by
  grind [Nat.add_one_mul_choose_eq]

/-- Sharp leading term for the fraction of polynomial coefficients in the
homogeneous kernel, normalized by degree and rank. -/
theorem hypersurface_kernel_ratio_lower {r d M s : ℕ} (hd : 0 < d) (hdM : d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M) :
    1 / ((d : ℝ) * (r + 1 : ℝ)) - 1 / (M : ℝ) ≤
        ((r + 1 + (M - d)).choose (M - d) : ℝ) / ((M : ℝ) * s) := by
  obtain ⟨hlo, hhi⟩ := hypersurface_rank_binomial_bounds hdM hr
  have hs := lt_of_lt_of_le
    (Nat.mul_pos hd (Nat.choose_pos (by omega))) hlo
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hM0 : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le hd hdM
  have hr0 : (0 : ℝ) < r + 1 := by positivity
  have hi := shifted_choose_successor_identity r M
  rw [Nat.choose_symm_add (a := r + 1) (b := M), ← hr] at hi
  have hR := congrArg (fun x : ℕ => (x : ℝ)) hi
  push_cast at hR
  have hh' : ((r : ℝ)+M+1)*s ≤ ((r : ℝ)+M+1)*d*((r+M).choose r : ℝ) := by exact_mod_cast (by simp_all [mul_assoc])
  apply (le_div_iff₀ (mul_pos hM0 hs0)).mpr
  field_simp
  nlinarith [mul_nonneg hr0.le hs0.le, congrArg (fun x : ℝ => d * x) hR]

end
end CCDN
