/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.RankNumerics

import Mathlib

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.AuxiliaryPolynomial.HypersurfaceRankProfile

/-! Exact leading term for the dimension root of the homogeneous Hilbert rank. -/

public section
namespace CCDN

/-- Taking the dimension root preserves the factorial leading coefficient. -/
theorem hypersurface_rank_root_bounds {r d M s : ℕ} (hrpos : 0 < r) (hdM : d ≤ M)
    (hr : HasHypersurfaceRank r d M s) :
    dimensionRoot r d * (↑M - d + 1) ≤
        ↑r.factorial ^ (1 / (r : ℝ)) * dimensionRoot r s ∧
      (r.factorial : ℝ) ^ (1 / (r : ℝ)) * dimensionRoot r s ≤
        dimensionRoot r d * ((M : ℝ) + r) := by
  obtain ⟨hl, hu⟩ := hypersurface_rank_power_bounds hdM hr
  have hfac : (0 : ℝ) < r.factorial := by positivity
  have hmd : 0 ≤ (M : ℝ) - d + 1 := by
    have : (d : ℝ) ≤ M := by exact_mod_cast hdM
    linarith
  have hl' := (div_le_iff₀ hfac).mp hl
  have hu' := (le_div_iff₀ hfac).mp hu
  have hlroot := Real.rpow_le_rpow (mul_nonneg (Nat.cast_nonneg d) (pow_nonneg hmd r)) hl'
    (show 0 ≤ 1 / ↑r by positivity)
  have huroot := Real.rpow_le_rpow
    (mul_nonneg (Nat.cast_nonneg s) hfac.le) hu' (show 0 ≤ 1 / ↑r by positivity)
  rw [Real.mul_rpow (Nat.cast_nonneg d) (pow_nonneg hmd r),
    Real.mul_rpow (Nat.cast_nonneg s) hfac.le, one_div,
    Real.pow_rpow_inv_natCast hmd hrpos.ne'] at hlroot
  rw [Real.mul_rpow (Nat.cast_nonneg s) hfac.le,
    Real.mul_rpow (Nat.cast_nonneg d) (by positivity), one_div,
    Real.pow_rpow_inv_natCast (by positivity) hrpos.ne'] at huroot
  constructor
  · grind
  · grind

end CCDN
