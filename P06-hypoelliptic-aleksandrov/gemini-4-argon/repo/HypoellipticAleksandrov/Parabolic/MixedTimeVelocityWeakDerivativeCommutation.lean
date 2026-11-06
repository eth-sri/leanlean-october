module

public import HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra

/-!
# Commutation of mixed time and velocity weak derivatives

This module derives a selected weak time derivative of a selected velocity
derivative from the corresponding velocity derivative of the selected weak
time derivative.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set

private theorem timeDerivative_hasCompactSupport
    {d } {f : TimeVelocity d → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (timeDerivative f) := by
  unfold timeDerivative
  simpa using hf.fderiv_apply (𝕜 := ℝ) ((1, 0) : TimeVelocity d)

private theorem velocityGradient_hasCompactSupport
    {d f} (k : Fin d)
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun z => velocityGradient f z k) := by
  unfold velocityGradient
  simpa using hf.fderiv_apply (𝕜 := ℝ)
    ((0, Pi.single k 1) : TimeVelocity d)

theorem hasWeakVelocityPartialDerivOn_of_hasWeakTimeDerivOn_velocityDeriv
    {d U} (k : Fin d)
    {u ut uk r }
    (hut : HasWeakTimeDerivOn U u ut)
    (huk : HasWeakVelocityPartialDerivOn U k u uk)
    (hukt : HasWeakTimeDerivOn U uk r) :
    HasWeakVelocityPartialDerivOn U k ut r := by
  intro φ hφ hφcompact hφU
  have _h_inl_6 : ContDiff ℝ (⊤ : ℕ∞) (timeDerivative φ) := by
    unfold timeDerivative
    exact (contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const
  have _h_inl_8 : tsupport (timeDerivative φ) ⊆ tsupport φ := by
    unfold timeDerivative
    change closure (Function.support (fun z => fderiv ℝ φ z (1, 0))) ⊆ tsupport φ
    refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
    intro z hz
    rw [Function.mem_support] at hz ⊢
    intro hzero
    apply hz
    simp [hzero]
  have htφ := huk (timeDerivative φ)
    _h_inl_6
    (timeDerivative_hasCompactSupport hφcompact)
    (_h_inl_8.trans hφU)
  have _h_inl_7 : ContDiff ℝ (⊤ : ℕ∞) (fun z => velocityGradient φ z k) := by
    unfold velocityGradient
    exact (contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const
  have _h_inl_9 : tsupport (fun z => velocityGradient φ z k) ⊆ tsupport φ := by
    unfold velocityGradient
    change closure (Function.support
      (fun z => fderiv ℝ φ z (0, Pi.single k 1))) ⊆ tsupport φ
    refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
    intro z hz
    rw [Function.mem_support] at hz ⊢
    intro hzero
    apply hz
    simp [hzero]
  have hkφ := hut (fun z => velocityGradient φ z k)
    _h_inl_7
    (velocityGradient_hasCompactSupport k hφcompact)
    (_h_inl_9.trans hφU)
  have huktφ := hukt φ hφ hφcompact hφU
  have hmixed : (∫ z in U, u z * velocityGradient (timeDerivative φ) z k
      ∂(volume : Measure (TimeVelocity d))) =
      ∫ z in U, u z * timeDerivative (fun w => velocityGradient φ w k) z
        ∂(volume : Measure (TimeVelocity d)) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      dsimp only
      have _h_inl_12 : velocityGradient (timeDerivative φ) z k =
      timeDerivative (fun w => velocityGradient φ w k) z := by
          have hgrad : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) :=
            (contDiff_infty_iff_fderiv.mp hφ).2
          have heval (a b : TimeVelocity d) :
              fderiv ℝ (fun x => fderiv ℝ φ x a) z b =
                fderiv ℝ (fderiv ℝ φ) z b a := by
            rw [fderiv_clm_apply (hgrad.differentiable (by simp) z)
              (differentiableAt_const (c := a))]
            rw [fderiv_const_apply]
            simp
          unfold timeDerivative velocityGradient
          rw [heval (1, 0) (0, Pi.single k 1),
            heval (0, Pi.single k 1) (1, 0)]
          have hfTwo : ContDiffAt ℝ 2 φ z :=
            hφ.contDiffAt.of_le (WithTop.coe_le_coe.mpr
              (show (2 : ℕ∞) ≤ ⊤ from le_top))
          exact (hfTwo.isSymmSndFDerivAt (by norm_num)).eq
            (0, Pi.single k 1) (1, 0)

        /- A selected weak time derivative of a selected velocity derivative is
        also the corresponding weak velocity derivative of the selected time
        derivative. -/
      rw [_h_inl_12]
  rw [hmixed, hkφ] at htφ
  linarith

end HypoellipticAleksandrov.Parabolic
