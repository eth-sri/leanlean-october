module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassQuadraticCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # One-dimensional diffused profile calculus for collar barriers -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Evolution

/-- A scalar velocity profile, written in the native diffused coordinate. -/
def reconstructionProfile (f : ℝ → ℝ) (p : Point) : ℝ := f (p.position 0)

variable {f : ℝ → ℝ}

/-- A twice smooth scalar profile has the required native slice regularity. -/
theorem reconstructionProfile_regular  (hf : ContDiff ℝ 2 f) (p : Point) :
    IsSliceRegularAt (reconstructionProfile f) p := by
  refine ⟨?_, ?_, ?_⟩
  · change DifferentiableAt ℝ (fun _ : ℝ => f (p.position 0)) p.time
    fun_prop
  · exact (hf.comp (contDiff_apply ℝ ℝ _)).contDiffAt
  · change ContDiffAt ℝ 2 (fun _ : PDE.Vec 1 => f (p.position 0)) p.velocity
    fun_prop

/-- A continuous scalar profile is continuous on native spacetime. -/
theorem reconstructionProfile_continuous  (hf : Continuous f) :
    Continuous (reconstructionProfile f) :=
  hf.comp ((continuous_apply 0).comp continuous_position)

private theorem profile_gradient  (hf : Differentiable ℝ f) (y : PDE.Vec 1) :
    PDE.classicalGradient (fun z : PDE.Vec 1 => f (z 0)) y =
      fun _ => deriv f (y 0) := by
  ext i
  have h := (hf _).hasDerivAt.comp_hasFDerivAt y (hasFDerivAt_apply (𝕜 := ℝ) 0 y)
  change fderiv ℝ _ y _ = _
  have hd : fderiv ℝ (fun z : PDE.Vec 1 => f (z 0)) y =
      deriv f (y 0) • ContinuousLinearMap.proj 0 := by
    simpa only [Function.comp_def] using! h.fderiv
  rw [hd]
  fin_cases i
  simp

private theorem profile_hessian  (hf : ContDiff ℝ 2 f) (y : PDE.Vec 1) :
    sliceHessian (fun z : PDE.Vec 1 => f (z 0)) y 0 0 = deriv (deriv f) (y 0) := by
  have hg : (fun z => PDE.classicalGradient (fun w : PDE.Vec 1 => f _) z) =
      fun z _ => deriv f _ :=
    funext (profile_gradient (hf.differentiable (by norm_num)))
  have h := (hf.differentiable_deriv_two _).hasDerivAt.comp_hasFDerivAt y
    (hasFDerivAt_apply (𝕜 := ℝ) 0 y)
  have hp := hasFDerivAt_pi.mpr (fun _ : Fin 1 => h)
  unfold sliceHessian
  have hd : fderiv ℝ (fun z : PDE.Vec 1 => fun _ : Fin 1 => deriv f (z 0)) y =
      ContinuousLinearMap.pi (fun _ : Fin 1 =>
        deriv (deriv f) (y 0) • ContinuousLinearMap.proj 0) := by
    simpa only [Function.comp_def] using! hp.fderiv
  simp_all

/-- The scalar profile operator is exactly the coefficient times its second derivative. -/
theorem reconstructionProfile_operator (a : ℝ → ℝ → ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (p : Point) :
    transportedForwardOperator (evolutionCoefficient a) (SectionTwo.identityDrift 1)
      (reconstructionProfile f) p = a (p.velocity 0) (p.position 0) *
        deriv (deriv f) (p.position 0) := by
  have hg : kineticVelocityGradient (reconstructionProfile f) p = 0 := by
    ext i
    change fderiv ℝ (fun _ : PDE.Vec 1 => f (p.position 0)) p.velocity _ = 0
    simp
  rw [transportedForwardOperator_apply, hg]
  simp only [kineticTimeDerivative, reconstructionProfile, deriv_const,
    PDE.vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, add_zero]
  rw [diffusedHessian_eq_sliceHessian]
  simp only [fullKineticCoefficientAt, evolutionCoefficient, matrixContraction,
    Fin.sum_univ_one, reconstructionProfile]
  rw [profile_hessian hf]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
