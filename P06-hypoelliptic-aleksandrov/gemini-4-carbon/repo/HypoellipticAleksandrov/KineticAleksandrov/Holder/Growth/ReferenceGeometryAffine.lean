module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometry
import Mathlib.Tactic

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder


/-- The affine image of the unit forward stack is the exact source stack. -/
theorem kineticAffine_image_forwardStack {d : ℕ} (P₀ : KineticPoint d)
    {R : ℝ} (hR : 0 < R) (m : ℕ) :
    kineticAffine P₀ R '' forwardStack (⟨0, 0, 0⟩ : KineticPoint d) 1 m =
      forwardStack P₀ R m  := by
  have kineticAffine_mem_forwardStack (P₀ P : KineticPoint d) {R : ℝ} (hR : 0 < R) (m : ℕ) :
      kineticAffine P₀ R P ∈ forwardStack P₀ R m ↔
      P ∈ forwardStack (⟨0, 0, 0⟩ : KineticPoint d) 1 m := by
    have hv := PDE.affine_mem_euclideanBall_iff_of_pos P₀.velocity P.velocity hR
    have hx : R ^ 3 • P.position ∈
        PDE.euclideanBall (0 : PDE.Vec d) (((m + 2 : ℕ) : ℝ) * R ^ 3) ↔
        P.position ∈ PDE.euclideanBall (0 : PDE.Vec d) ((m + 2 : ℕ) : ℝ) := by
      have hm : 0 < ((m + 2 : ℕ) : ℝ) := by positivity
      rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (mul_pos hm (pow_pos hR 3)),
        PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hm]
      simp only [sub_zero, PDE.vecEuclideanNorm_smul, abs_of_pos (pow_pos hR 3)]
      rw [mul_comm ((m + 2 : ℕ) : ℝ), mul_lt_mul_iff_right₀ (pow_pos hR 3)]
    simp only [mem_forwardStack_iff, kineticAffine_time, kineticAffine_velocity,
      relativePosition_kineticAffine, one_pow]
    simp only [relativePosition, sub_zero, smul_zero, mul_one]
    rw [add_comm P₀.velocity, hv]
    rw [hx]
    have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
    constructor
    · rintro ⟨ha, hb, hv', hx'⟩
      refine ⟨?_, ?_, hv', hx'⟩ <;> nlinarith
    · rintro ⟨ha, hb, hv', hx'⟩
      refine ⟨?_, ?_, hv', hx'⟩ <;> nlinarith
  ext P
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact (kineticAffine_mem_forwardStack P₀ Q hR m).mpr hQ
  · intro hP
    refine ⟨kineticAffineInverse P₀ R P, ?_, kineticAffine_apply_inverse P₀ hR.ne' P⟩
    apply (kineticAffine_mem_forwardStack P₀ _ hR m).mp
    simpa only [kineticAffine_apply_inverse P₀ hR.ne' P] using hP

end HypoellipticAleksandrov.KineticAleksandrov.Holder

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

/-- Composing kinetic affine maps transports an arbitrary source cylinder exactly. -/
theorem kineticAffine_image_cylinder {d : ℕ} (P0 P : KineticPoint d)
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r) :
    kineticAffine P0 R '' backwardCylinder P r =
      backwardCylinder (kineticAffine P0 R P) (R * r) := by
  rw [← kineticAffine_image_unitCylinder P hr, image_image, ← Function.comp_def,
    kineticAffine_comp,
    kineticAffine_image_unitCylinder _ (mul_pos hR hr)]

/-- The exact source stack identity is preserved by arbitrary affine composition. -/
theorem kineticAffine_image_stack {d : ℕ} (P0 P : KineticPoint d)
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r) (m : ℕ) :
    kineticAffine P0 R '' forwardStack P r m =
      forwardStack (kineticAffine P0 R P) (R * r) m := by
  rw [← kineticAffine_image_forwardStack P hr m, image_image, ← Function.comp_def,
    kineticAffine_comp,
    kineticAffine_image_forwardStack _ (mul_pos hR hr) m]

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

