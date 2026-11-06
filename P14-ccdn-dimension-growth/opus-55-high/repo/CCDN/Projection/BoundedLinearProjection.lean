/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Height.ProjectiveBox
import CCDN.Algebra.BoundedRowSeparation
import CCDN.Height.ProjectiveIntegerHeight

/-! An explicit integral linear projection away from a bounded rational
linear center. Its kernel is exactly the span of the given independent
rows, and its coefficient bound is uniform in their entries. -/

namespace CCDN
section
open Matrix

variable {m n : ℕ}

theorem integer_linear_map_box_bound
    (P : Matrix (Fin m) (Fin n) ℤ) {H B : ℝ} (hH : 0 ≤ H)
    (hP : ∀ i j, |(P i j : ℝ)| ≤ H)
    (z : IntPoint n) (hz : InBox z B) :
    ∀ i, |((P *ᵥ z) i : ℝ)| ≤ (n : ℝ) * H * B := by
  intro i
  simp [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul]
  calc
    _ ≤ ∑ j, |(P i j : ℝ) * (z j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, H * B := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hP i j) (hz j) (abs_nonneg _) hH
    _ = _ := by simp [mul_assoc]

lemma rationalPoint_integer_mulVec
    (P : Matrix (Fin m) (Fin n) ℤ) (z : IntPoint n) :
    rationalPoint (P *ᵥ z) =
      (P.map (Int.castRingHom ℚ)) *ᵥ rationalPoint z := by
  funext i
  simp [rationalPoint, Matrix.mulVec, dotProduct]

/-- The height estimate for the projective linear image of any
point outside the matrix kernel. The input height is its intrinsic
multiplicative projective height. -/
theorem projective_linear_map_height
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
  have hw : rationalPoint w =
      (c : ℚ) • ((P.map (Int.castRingHom ℚ)) *ᵥ x.rep) := by
    rw [rationalPoint_integer_mulVec]
    rw [← hc, Matrix.mulVec_smul]
    rfl
  have hw0 : w ≠ 0 := by
    intro hz
    have hzero : (c : ℚ) • ((P.map (Int.castRingHom ℚ)) *ᵥ x.rep) = 0 := by
      rw [← hw, hz]
      rfl
    simp_all
  have hproj :
      Projectivization.mk ℚ (rationalPoint w) (rationalPoint_ne_zero hw0) =
        Projectivization.mk ℚ ((P.map (Int.castRingHom ℚ)) *ᵥ x.rep) himage := by
    apply (Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).mpr
    exact ⟨c, hw.symm⟩
  rw [← hproj]
  exact projective_integer_height_le _ hw0 (integer_linear_map_box_bound P hH hP z (primitiveProjectiveRep_bound x))

