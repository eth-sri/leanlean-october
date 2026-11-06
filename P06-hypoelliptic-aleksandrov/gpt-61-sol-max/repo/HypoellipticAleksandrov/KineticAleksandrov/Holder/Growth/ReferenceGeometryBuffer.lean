module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackCorridors
import Mathlib.Tactic

/-! # Additional lower-time buffer in the source reference set

The author-buffer replaces the false strict bound -(m+4) by -(m+5).
Its physical image is kept inside the original comparison cylinder by a smaller scale.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

variable (d m : ℕ)

/-- The author-reference box with one extra unit of lower-time buffer. -/
def referenceRegion  (L : ℝ) : Set (KineticPoint d) :=
  {P | -((m : ℝ) + 5) < P.time ∧ P.time < 0 ∧
    PDE.vecEuclideanNorm P.position < L ∧ PDE.vecEuclideanNorm P.velocity < L}

/-- A sufficiently small scale places the buffered reference set inside the unit cylinder. -/
theorem referenceRegion_scaled_subset_unit  {L eps : ℝ}
    (heps : 0 < eps) (heps1 : eps ≤ 1) (ht : eps * ((m : ℝ) + 5) < 1)
    (hspace : eps * L < 1) :
    kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps '' referenceRegion d m L ⊆
      backwardCylinder (⟨0, 0, 0⟩ ) 1 := by
  have heps2 : eps ^ 2 ≤ eps := by nlinarith only [heps.le, heps1]

  rintro _ ⟨P, hP, rfl⟩
  obtain ⟨hlo, hhi, hx, hv⟩ := hP

  refine ⟨?_, ?_, ?_, ?_⟩
  · change (0 : ℝ) - 1 ^ 2 < 0 + eps ^ 2 * P.time

    norm_num only [one_pow, zero_sub, zero_add]
    linarith only [(mul_lt_mul_of_pos_left hlo (pow_pos heps 2)), ((mul_le_mul_of_nonneg_right heps2 (by positivity)).trans_lt ht)]
  · change 0 + eps ^ 2 * P.time < (0 : ℝ)
    simpa only [zero_add] using mul_neg_of_pos_of_neg (pow_pos heps 2) hhi
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num : (0 : ℝ) < 1)).mpr
    change PDE.vecEuclideanNorm (0 + eps • P.velocity - 0) < 1
    rw [zero_add, sub_zero, PDE.vecEuclideanNorm_smul, abs_of_pos heps]
    exact (mul_lt_mul_of_pos_left hv heps).trans hspace
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by norm_num : (0 : ℝ) < 1 ^ 3)).mpr
    have hrel : relativePosition (⟨0, 0, 0⟩ : KineticPoint d)
        (kineticAffine ⟨0, 0, 0⟩ eps P) = eps ^ 3 • P.position := by
      simp
    rw [hrel, sub_zero, PDE.vecEuclideanNorm_smul, abs_of_pos (pow_pos heps 3)]
    norm_num only [one_pow]

    exact ((mul_le_mul_of_nonneg_right (by

        nlinarith only [(mul_le_mul_of_nonneg_right heps2 heps.le), heps2]) (PDE.vecEuclideanNorm_nonneg P.position)).trans_lt
      (mul_lt_mul_of_pos_left hx heps)).trans hspace

/-- Every finite positive spatial bound admits a scale preserving the unit domain. -/
theorem exists_buffered_reference_scale  {L : ℝ} (hL : 0 < L) :
    ∃ eps : ℝ, 0 < eps ∧ eps < 1 ∧
      kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps '' referenceRegion d m L ⊆
        backwardCylinder (⟨0, 0, 0⟩ ) 1 := by
  let D := 2 * ((m : ℝ) + 5 + L + 1)
  let eps := D⁻¹
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hD : 0 < D := by dsimp only [D]; linarith only [hm, hL]
  have heps  := inv_pos.mpr hD
  have heq  := inv_mul_cancel₀ hD.ne'

  have heps1 : eps < 1 := by
    have he := mul_lt_mul_of_pos_left (show 1 < D by dsimp only [D]; linarith only [hm, hL]) heps
    rw [mul_one, heq] at he
    exact he


  exact ⟨eps, heps, heps1,
    referenceRegion_scaled_subset_unit d m heps heps1.le (by

        exact (mul_lt_mul_of_pos_left (by dsimp only [D]; linarith only [hm, hL]) heps).trans_eq heq) ((mul_lt_mul_of_pos_left (by dsimp only [D]; linarith only [hm, hL]) heps).trans_eq heq)⟩

/-- Reference-set containment automatically preserves the admissibility domain. -/
theorem buffered_reference_preserves_domain {d : ℕ} (P0 : KineticPoint d) {R eps L : ℝ}
    (hR : 0 < R) (m : ℕ)
    (hunit : kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps '' referenceRegion d m L ⊆
      backwardCylinder (⟨0, 0, 0⟩ ) 1)
    (O : Set (KineticPoint d)) (hO : closure (backwardCylinder P0 R) ⊆ O) :
    closure (kineticAffine P0 (R * eps) '' referenceRegion d m L) ⊆ O := by
  apply (closure_mono ?_).trans hO
  rw [← kineticAffine_image_unitCylinder P0 hR]
  rintro _ ⟨P, hP, rfl⟩
  have hcomp := congrFun (kineticAffine_comp P0 (⟨0, 0, 0⟩ ) R eps) P
  have hzero : kineticAffine P0 R (⟨0, 0, 0⟩ ) = P0 := by
    simp only [kineticAffine, mul_zero, smul_zero, zero_smul, add_zero]
  rw [hzero] at hcomp
  exact ⟨_, hunit ⟨P, hP, rfl⟩, hcomp⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
