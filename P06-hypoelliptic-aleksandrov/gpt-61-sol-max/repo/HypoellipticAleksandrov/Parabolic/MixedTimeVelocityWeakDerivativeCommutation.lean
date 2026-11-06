module

public import HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
import all HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Calculus.RegularityOrder



open private HypoellipticAleksandrov.Parabolic.timeDerivative_tsupport from HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
open private HypoellipticAleksandrov.Parabolic.timeDerivative_compact from HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
section
open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_tsupport_subset from HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
private alias _sharedProof_198_1 := HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_tsupport_subset
end


/-!
# Commutation of mixed time and velocity weak derivatives

This module derives a selected weak time derivative of a selected velocity
derivative from the corresponding velocity derivative of the selected weak
time derivative.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

private alias timeDerivative_tsupport_subset :=
  _root_.HypoellipticAleksandrov.Parabolic.timeDerivative_tsupport

open MeasureTheory Set

variable {d : ℕ}

variable {f : HypoellipticAleksandrov.Parabolic.ScalarField d}

private theorem timeDerivative_contDiff_infty

    (hf : ContDiff ℝ PDE.smoothOrder f) :
    ContDiff ℝ PDE.smoothOrder (timeDerivative f) := by
  unfold timeDerivative
  exact (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

private theorem velocityGradient_contDiff_infty
      (k : Fin d)
    (hf : ContDiff ℝ PDE.smoothOrder f) :
    ContDiff ℝ PDE.smoothOrder (fun z => velocityGradient f z k) := by
  unfold velocityGradient
  exact (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const



private theorem velocityGradient_hasCompactSupport
      (k : Fin d)
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun z => velocityGradient f z k) := (id (HasCompactSupport.fderiv_apply ℝ hf (0, Pi.single k 1)))

variable (f : HypoellipticAleksandrov.Parabolic.ScalarField d)




private theorem velocityGradient_tsupport_subset
      (k : Fin d) :
    tsupport (fun z => velocityGradient f z k) ⊆ tsupport f := _sharedProof_198_1


private theorem time_velocity_derivative_commute

    (hf : ContDiff ℝ PDE.smoothOrder f) (k : Fin d) (z : TimeVelocity d) :
    velocityGradient (timeDerivative f) z k =
      timeDerivative (fun w => velocityGradient f w k) z := by

  have heval (a b : TimeVelocity d) :
      fderiv ℝ (fun x => fderiv ℝ f x a) z b =
        fderiv ℝ (fderiv ℝ f) z b a := by
    rw [fderiv_clm_apply (((contDiff_infty_iff_fderiv.mp hf).2).differentiable (by simp) z)
      (differentiableAt_const (c := a))]
    rw [fderiv_const_apply]
    simp
  unfold timeDerivative velocityGradient
  rw [heval (1, 0) (0, Pi.single k 1),
    heval (0, Pi.single k 1) (1, 0)]
  have hfTwo : ContDiffAt ℝ 2 f z :=
    hf.contDiffAt.of_le (WithTop.coe_le_coe.mpr
      (show (2 : ℕ∞) ≤ ⊤ from le_top))
  exact (hfTwo.isSymmSndFDerivAt (by norm_num)).eq
    (0, Pi.single k 1) (1, 0)

/-- A selected weak time derivative of a selected velocity derivative is
also the corresponding weak velocity derivative of the selected time
derivative. -/
theorem hasWeakVelocityPartialDerivOn_of_hasWeakTimeDerivOn_velocityDeriv
     {U : HypoellipticAleksandrov.Parabolic.Region d} (k : Fin d)
    {u ut uk r : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hut : HasWeakTimeDerivOn U u ut)
    (huk : HasWeakVelocityPartialDerivOn U k u uk)
    (hukt : HasWeakTimeDerivOn U uk r) :
    HasWeakVelocityPartialDerivOn U k ut r := by
  intro φ hφ hφcompact hφU
  have htφ := huk _
    (timeDerivative_contDiff_infty hφ)
    (_root_.HypoellipticAleksandrov.Parabolic.timeDerivative_compact hφcompact)
    ((_root_.HypoellipticAleksandrov.Parabolic.timeDerivative_tsupport φ).trans hφU)
  have hkφ := hut (fun z => velocityGradient φ z k)
    (velocityGradient_contDiff_infty k hφ)
    (velocityGradient_hasCompactSupport k hφcompact)
    ((velocityGradient_tsupport_subset φ k).trans hφU)
  have huktφ := hukt φ hφ hφcompact hφU
  have hmixed : (∫ z in U, u z * velocityGradient (timeDerivative φ) z k
      ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      ∫ z in U, u z * timeDerivative (fun w => velocityGradient φ w k) z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      simp_all [time_velocity_derivative_commute]
  rw [hmixed, hkφ] at htφ
  linarith

end HypoellipticAleksandrov.Parabolic
