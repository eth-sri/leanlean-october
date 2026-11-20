module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileSpectralJets

/-! # Homogeneity of the full velocity Hessian and stationary transport -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

section
variable {d : ℕ} (alpha : ℝ) (H : XV d → ℝ) (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ))
  (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) (r : ℝ) (hr : 0 < r)
  (q : XV d) (hq : q ≠ 0)
include hsmooth hhom hr hq

/-- The velocity Hessian has the exact kinetic weight alpha minus two. -/
theorem homogeneous_dvv :
    dvv H (dilate r q) = Real.rpow r (alpha - 2) • dvv H q := by
  ext i k
  exact homogeneous_dvv_off_origin H alpha r hr (hhom r hr) hsmooth q hq i k

/-- The actual stationary transport has the same kinetic weight as the velocity Hessian. -/
theorem homogeneous_transport :
    PDE.vecDot (dilate r q).2 (dx H (dilate r q)) =
      Real.rpow r (alpha - 2) * PDE.vecDot q.2 (dx H q) := by
  rw [transport_eq_direction, transport_eq_direction]
  have hdir : ((dilate r q).2, (0 : PDE.Vec d)) = r • ((q.2, 0) : XV d) := by
    simp only [dilate, Prod.smul_mk, smul_zero]
  rw [hdir, map_smul, smul_eq_mul,
    homogeneous_position_direction q.2 hr (Filter.Eventually.of_forall (hhom r hr))
      (differentiableAt_profile_off_origin H hsmooth q hq)
      (differentiableAt_profile_off_origin H hsmooth _ (dilate_ne_zero r hr q hq))]
  have hp : r * Real.rpow r (alpha - 3) = Real.rpow r (alpha - 2) := by
    simp only [Real.rpow_eq_pow]
    conv_lhs => lhs; rw [← Real.rpow_one r]
    rw [← Real.rpow_add hr]
    congr 1
    ring
  rw [← mul_assoc, hp]

end

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
