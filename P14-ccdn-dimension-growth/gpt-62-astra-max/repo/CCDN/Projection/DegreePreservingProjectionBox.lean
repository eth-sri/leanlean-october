/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Projection.BoundedBirationalHypersurfaceProjection
public import CCDN.Height.Box
import CCDN.Projection.BoundedLinearProjection

/-! The polynomial box enlargement for bounded integer projections to the plane. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

section

variable (n d : ℕ)

/-- A bound for the operator norm of the projection matrix. -/
def projectionBoxFactor : ℝ :=
  (n+1) * birationalProjectionHeightConstant n * (d+1 : ℝ)^(2*n)

lemma projectionBoxFactor_one_le : 1 ≤ projectionBoxFactor n d := by
  have hC : (1 : ℝ) ≤ birationalProjectionHeightConstant n := by exact_mod_cast birationalProjectionHeightConstant_pos n
  apply one_le_mul_of_one_le_of_one_le (by bound)
  bound

end

variable {m n d : ℕ} (P : Matrix (Fin m) (Fin n) ℤ)

lemma degreeProjection_box (hd : 0 < d)
    (hP : ∀ i j, |P i j| ≤ integerBirationalProjectionHeight n d)
    {B : ℝ} (hB : 0 ≤ B) {z : IntPoint n} (hz : InBox z B) :
    InBox (P *ᵥ z) (projectionBoxFactor n d * B) := by
  have hh := integer_linear_map_box_bound P (H := integerBirationalProjectionHeight n d) (by positivity)
    (by norm_cast) z hz
  intro i
  apply (hh i).trans
  gcongr
  have h : (integerBirationalProjectionHeight n d : ℝ) ≤ birationalProjectionHeightConstant n * (d : ℝ) ^ (2*n) := by
    exact_mod_cast integerBirationalProjectionHeight_le n d hd
  unfold projectionBoxFactor
  rw [mul_assoc]
  gcongr
  · linarith
  · apply h.trans
    gcongr
    linarith

lemma rationalPoint_integer_projection (z : IntPoint n) :
    rationalPoint (P *ᵥ z) = fun j => eval (rationalPoint z) (integerLinearForm (P j)) := by
  funext j
  simp [rationalPoint, Matrix.mulVec, dotProduct]

end
end CCDN
