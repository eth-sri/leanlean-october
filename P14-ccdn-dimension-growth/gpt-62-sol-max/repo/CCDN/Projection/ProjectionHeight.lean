/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.BoundedBirationalHypersurfaceProjection
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A common box enlargement for the bounded affine and projective curve projections. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- Real coefficient bound for the matrix of a bounded projection. -/
def projectionEntryBound (n d : ℕ) : ℝ :=
  birationalProjectionHeightConstant n * ((d : ℝ) + 1) ^ (2 * n)

lemma projectionEntryBound_one_le (n d : ℕ) : 1 ≤ projectionEntryBound n d := by
  apply one_le_mul_of_one_le_of_one_le
  · exact_mod_cast Nat.succ_le_of_lt (birationalProjectionHeightConstant_pos n)
  · exact one_le_pow₀ (le_add_of_nonneg_left (by positivity))

lemma projectionEntryBound_le {n d : ℕ} (hd : 0 < d) {a : ℤ}
    (ha : |a| ≤ integerBirationalProjectionHeight n d) : |(a : ℝ)| ≤ projectionEntryBound n d := by
  have h := ha.trans (Int.ofNat_le.mpr (integerBirationalProjectionHeight_le n d hd))
  calc
    _ ≤ (birationalProjectionHeightConstant n : ℝ) * (d : ℝ) ^ (2 * n) := by exact_mod_cast h
    _ ≤ _ := by
      unfold projectionEntryBound
      gcongr
      exact le_add_of_nonneg_right zero_le_one

/-- Scaling factor for boxes and projective heights under the bounded linear projection. -/
def projectionBoxFactor (n d : ℕ) : ℝ := ((n : ℝ) + 1) * projectionEntryBound n d

lemma projectionBoxFactor_one_le (n d : ℕ) : 1 ≤ projectionBoxFactor n d :=
  one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_left (by positivity)) (projectionEntryBound_one_le n d)

end
end CCDN
