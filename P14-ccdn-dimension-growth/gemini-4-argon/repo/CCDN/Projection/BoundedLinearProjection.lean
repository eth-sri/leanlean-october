/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.ProjectiveBox
import CCDN.Height.ProjectiveIntegerHeight
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! An explicit integral linear projection away from a bounded rational
linear center. Its kernel is exactly the span of the given independent
rows, and its coefficient bound is uniform in their entries. -/

@[expose] public section
namespace CCDN
noncomputable section
open Matrix

/-- The height estimate for the projective linear image of any
point outside the matrix kernel. The input height is its intrinsic
multiplicative projective height. -/
theorem projective_linear_map_height {m n : ℕ}
    (P : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ)
    {H : ℝ} (hH : 0 ≤ H) (hP : ∀ i j, |(P i j : ℝ)| ≤ H)
    (x : ProjectivePoint n)
    (himage : (P.map (Int.castRingHom ℚ)) *ᵥ x.rep ≠ 0) :
    (Projectivization.mk ℚ ((P.map (Int.castRingHom ℚ)) *ᵥ x.rep) himage).mulHeight ≤
      (n + 1 : ℕ) * H * x.mulHeight := by
  let z := primitiveProjectiveRep x
  let w := P *ᵥ z
  have hrep := (primitiveProjectiveRep_mk x).trans x.mk_rep.symm
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℚ _ _ _ _).mp hrep
  have hw : rationalPoint w = (c : ℚ) • ((P.map (Int.castRingHom ℚ)) *ᵥ x.rep) := by
    rw [show rationalPoint w = (P.map (Int.castRingHom ℚ)) *ᵥ rationalPoint z by
      funext i; simp [w, rationalPoint, Matrix.mulVec, dotProduct]]
    change (P.map (Int.castRingHom ℚ)) *ᵥ rationalPoint (primitiveProjectiveRep x) = _
    rw [← hc, Matrix.mulVec_smul]
    rfl
  have hw0 : w ≠ 0 := fun hz => himage ((smul_eq_zero.mp (by rw [← hw, hz]; rfl)).resolve_left c.ne_zero)
  have hproj :
      Projectivization.mk ℚ (rationalPoint w) (rationalPoint_ne_zero hw0) =
        Projectivization.mk ℚ ((P.map (Int.castRingHom ℚ)) *ᵥ x.rep) himage :=
    (Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).mpr ⟨c, hw.symm⟩
  rw [← hproj]
  refine projective_integer_height_le _ hw0 fun i => ?_
  simp only [w, Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul]
  calc
    _ ≤ ∑ j, |(P i j : ℝ) * (z j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin (n + 1), H * x.mulHeight := Finset.sum_le_sum fun j _ => by
      rw [abs_mul]
      exact mul_le_mul (hP i j) (primitiveProjectiveRep_bound x j) (abs_nonneg _) hH
    _ = _ := by simp [mul_assoc]

end
end CCDN
