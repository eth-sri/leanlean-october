module

public import HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra

/-!
# Commutation of mixed time and velocity weak derivatives

This module derives a selected weak time derivative of a selected velocity
derivative from the corresponding velocity derivative of the selected weak
time derivative.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set

variable {d : ℕ} {f : TimeVelocity d → ℝ} (k : Fin d)

private theorem timeDerivative_contDiff_infty
    
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (timeDerivative f) := (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

private theorem velocityGradient_contDiff_infty
    
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => velocityGradient f z k) := (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

private theorem timeDerivative_hasCompactSupport
     (hf : HasCompactSupport f) :
    HasCompactSupport (timeDerivative f) := by
  unfold timeDerivative
  simpa using hf.fderiv_apply (𝕜 := ℝ) _

private theorem velocityGradient_hasCompactSupport
    
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun z => velocityGradient f z k) := by
  unfold velocityGradient
  simpa using hf.fderiv_apply (𝕜 := ℝ)
    _

private theorem timeDerivative_tsupport_subset
     (f : TimeVelocity d → ℝ) :
    tsupport (timeDerivative f) ⊆ tsupport f := by
  unfold timeDerivative
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  aesop

private theorem velocityGradient_tsupport_subset
     (f : TimeVelocity d → ℝ) (k : Fin d) :
    tsupport (fun z => velocityGradient f z k) ⊆ tsupport f := by
  unfold velocityGradient
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  aesop

private theorem time_velocity_derivative_commute
     (f : TimeVelocity d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : Fin d) (z : TimeVelocity d) :
    velocityGradient (timeDerivative f) z k =
      timeDerivative (fun w => velocityGradient f w k) z := by
  have hgrad : ContDiff ℝ _ (fderiv ℝ f) :=
    (contDiff_infty_iff_fderiv.mp hf).2
  have heval (a b : TimeVelocity d) :
      fderiv ℝ (fun x => fderiv ℝ f x a) z b =
        fderiv ℝ (fderiv ℝ f) z b a := by
    rw [fderiv_clm_apply (hgrad.differentiable (by simp) z)
      (differentiableAt_const (c := a))]
    simp
  unfold timeDerivative velocityGradient
  rw [heval,
    heval]
  have hfTwo : ContDiffAt ℝ 2 f z :=
    hf.contDiffAt.of_le (WithTop.coe_le_coe.mpr
      (show (2) ≤ ⊤ from le_top))
  exact (hfTwo.isSymmSndFDerivAt (by norm_num)).eq
    _ _

/-- A selected weak time derivative of a selected velocity derivative is
also the corresponding weak velocity derivative of the selected time
derivative. -/
theorem hasWeakVelocityPartialDerivOn_of_hasWeakTimeDerivOn_velocityDeriv
     {U : Set (TimeVelocity d)} (k : Fin d)
    {u ut uk r : TimeVelocity d → ℝ}
    (hut : HasWeakTimeDerivOn U u ut)
    (huk : HasWeakVelocityPartialDerivOn U k u uk)
    (hukt : HasWeakTimeDerivOn U uk r) :
    HasWeakVelocityPartialDerivOn U k ut r := by
  intro φ hφ hφcompact hφU
  have htφ := huk _
    (timeDerivative_contDiff_infty hφ)
    (timeDerivative_hasCompactSupport hφcompact)
    ((timeDerivative_tsupport_subset φ).trans hφU)
  have hkφ := hut _
    (velocityGradient_contDiff_infty k hφ)
    (velocityGradient_hasCompactSupport k hφcompact)
    ((velocityGradient_tsupport_subset φ k).trans hφU)
  have huktφ := hukt φ hφ hφcompact hφU
  have hmixed : (∫ z in U, u z * velocityGradient (timeDerivative φ) z k
      ∂volume) =
      ∫ z in U, u z * timeDerivative (fun w => velocityGradient φ w k) z
        ∂volume := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      dsimp only
      rw [time_velocity_derivative_commute φ hφ]
  linarith

end HypoellipticAleksandrov.Parabolic
