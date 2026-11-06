module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometry
import Mathlib.Tactic

/-! # Exact affine scaling of the source forward stack -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

/-- Membership in a forward stack is transported from the source unit stack. -/
theorem kineticAffine_mem_forwardStack {d : ℕ} (P₀ P : KineticPoint d)
    {R : ℝ} (hR : 0 < R) (m : ℕ) :
    kineticAffine P₀ R P ∈ forwardStack P₀ R m ↔
      P ∈ forwardStack (⟨0, 0, 0⟩ : KineticPoint d) 1 m := by
  let sharedTerm_d68893c3d0 := (((m + 2 : ℕ) : ℝ))

  have hx : R ^ 3 • P.position ∈
      PDE.euclideanBall (0 : PDE.Vec d) (sharedTerm_d68893c3d0 * R ^ 3) ↔
      P.position ∈ PDE.euclideanBall (0 : PDE.Vec d) sharedTerm_d68893c3d0 := by
    have hm : 0 < sharedTerm_d68893c3d0 := by positivity
    rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (mul_pos hm (pow_pos hR 3)),
      PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hm]
    simp only [sub_zero, PDE.vecEuclideanNorm_smul, abs_of_pos (pow_pos hR 3)]
    rw [mul_comm sharedTerm_d68893c3d0, mul_lt_mul_iff_right₀ (pow_pos hR 3)]
  simp only [mem_forwardStack_iff, kineticAffine_time, kineticAffine_velocity,
    relativePosition_kineticAffine, one_pow]
  simp only [relativePosition, sub_zero, smul_zero, mul_one]
  rw [add_comm P₀.velocity, (PDE.affine_mem_euclideanBall_iff_of_pos P₀.velocity P.velocity hR)]
  rw [hx]
  have hR2  := sq_pos_of_pos hR
  constructor
  · rintro ⟨ha, hb, hv', hx'⟩
    refine ⟨?_, ?_, hv', hx'⟩ <;> nlinarith
  · rintro ⟨ha, hb, hv', hx'⟩
    refine ⟨?_, ?_, hv', hx'⟩ <;> nlinarith

/-- The affine image of the unit forward stack is the exact source stack. -/
theorem kineticAffine_image_forwardStack {d : ℕ} (P₀ : KineticPoint d)
    {R : ℝ} (hR : 0 < R) (m : ℕ) :
    kineticAffine P₀ R '' forwardStack (⟨0, 0, 0⟩ ) 1 m =
      forwardStack P₀ R m := by
  ext P
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact (kineticAffine_mem_forwardStack P₀ Q hR m).mpr hQ
  · intro hP
    refine ⟨kineticAffineInverse P₀ R P, ?_, kineticAffine_apply_inverse P₀ hR.ne' P⟩
    apply (kineticAffine_mem_forwardStack P₀ _ hR m).mp
    simpa only [kineticAffine_apply_inverse P₀ hR.ne' P] using hP

end HypoellipticAleksandrov.KineticAleksandrov.Holder
