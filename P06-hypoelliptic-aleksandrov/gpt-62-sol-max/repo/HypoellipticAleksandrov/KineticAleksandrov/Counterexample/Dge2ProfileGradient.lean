module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoHomogeneity

/-! # Exact homogeneity and gauge bound for the velocity gradient -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

section
variable {d : ℕ} (alpha : ℝ) (H : XV d → ℝ) (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ))
  (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q)
include hsmooth hhom

section
variable (r : ℝ) (hr : 0 < r) (q : XV d) (hq : q ≠ 0)
include hr hq

/-- The derivative of a homogeneous smooth function has the source velocity weight. -/
theorem homogeneous_velocity_jet (w : PDE.Vec d) :
    fderiv ℝ H (dilate r q) (0, w) =
      Real.rpow r (alpha - 1) * fderiv ℝ H q (0, w) := homogeneous_velocity_direction w hr (Filter.Eventually.of_forall (hhom r hr))
    (differentiableAt_profile_off_origin H hsmooth q hq)
    (differentiableAt_profile_off_origin H hsmooth _ (dilate_ne_zero r hr q hq))

/-- The native selector vector has the same exact velocity homogeneity. -/
theorem homogeneous_dv :
    dv H (dilate r q) = Real.rpow r (alpha - 1) • dv H q := by
  ext i
  exact homogeneous_velocity_jet alpha H hsmooth hhom r hr q hq (Pi.single i 1)

end

/-- Smooth homogeneous profiles satisfy the source velocity-gradient bound. -/
theorem homogeneous_velocity_gradient_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ q, q ≠ 0 →
      PDE.vecEuclideanNorm (dv H q) ≤ C * Real.rpow (rho q) (alpha - 1) := by
  let K : Set (XV d) := {q | rho q = 1}
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hd : ContinuousOn (fun q => PDE.vecEuclideanNorm (dv H q)) K := by
    apply PDE.continuous_vecEuclideanNorm.comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    have hc := (hsmooth.continuousOn_fderiv_of_isOpen hopen (by simp)).clm_apply
      (continuousOn_const (c := ((0, Pi.single i 1) : XV d)))
    exact hc.mono (fun _ hq => ne_zero_of_rho_eq_one hq)
  obtain ⟨B, hB⟩ := (isCompact_unitGaugeShell d).bddAbove_image hd
  let C := max 1 B
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro q hq
  have hr : 0 < rho q := (rho_nonneg q).lt_of_ne' ((rho_eq_zero_iff q).not.mpr hq)
  have hj := homogeneous_dv alpha H hsmooth hhom (rho q) hr
    (normalizeGauge q) (normalizeGauge_ne_zero q hq)
  rw [dilate_normalizeGauge q hq] at hj
  rw [hj, PDE.vecEuclideanNorm_smul]
  have hpow := Real.rpow_pos_of_pos hr (alpha - 1)
  simp only [Real.rpow_eq_pow] at hpow ⊢
  rw [abs_of_pos hpow]
  have hb : PDE.vecEuclideanNorm (dv H (normalizeGauge q)) ≤ C :=
    (hB ⟨normalizeGauge q, rho_normalizeGauge q hq, rfl⟩).trans (le_max_right _ _)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb hpow.le

end

/-- The actual profile satisfies the required velocity-gradient estimate. -/
theorem geometricProfile_velocity_gradient_bound {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : XV d, q ≠ 0 →
      PDE.vecEuclideanNorm (dv (geometricProfile alpha C₀ sigma R) q) ≤
        C * Real.rpow (rho q) (alpha - 1) := by
  apply homogeneous_velocity_gradient_bound alpha (geometricProfile alpha C₀ sigma R)
    (geometricProfile_smooth_off_origin alpha C₀ sigma R hsigma hR)
  exact fun r hr q => geometricProfile_homogeneous alpha C₀ sigma R r hr q

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
