module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # Constant shifts in the classical kinetic comparison argument -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic Set

variable {d : ℕ}

variable (c : ℝ)

/-- All classical kinetic derivatives of a constant vanish. -/
theorem comparison_const_formulas   (P : KineticPoint d) :
    kineticTimeDerivative (fun _ : KineticPoint d => c) P = 0 ∧
    kineticPositionGradient (fun _ : KineticPoint d => c) P = 0 ∧
    kineticVelocityGradient (fun _ : KineticPoint d => c) P = 0 ∧
    kineticVelocityHessian (fun _ : KineticPoint d => c) P = 0 := by
  refine ⟨deriv_const _ _,?_,?_,?_⟩
  · ext i
    simp [kineticPositionGradient, PDE.classicalGradient]
  · ext i
    simp [kineticVelocityGradient, PDE.classicalGradient]
  · have hg : (PDE.classicalGradient (fun _ : PDE.Vec d => c)) =
        fun _ => 0 := by
      funext v
      ext i
      simp [PDE.classicalGradient]
    unfold kineticVelocityHessian
    rw [hg]
    ext i j
    simp

/-- Constants belong to the exact anisotropic kinetic classical class on every set. -/
theorem comparison_regular_const   (D : Set (KineticPoint d)) :
    IsKineticC112On (fun _ : KineticPoint d => c) D := by
  let sharedTerm_6b1496b636 := ((fun _ : KineticPoint d => c))
  refine ⟨continuousOn_const,fun _ _ => differentiableAt_const c,
    fun _ _ => contDiffAt_const,fun _ _ => contDiffAt_const,?_,?_,?_,?_⟩
  · have h : kineticTimeDerivative sharedTerm_6b1496b636 = fun _ => 0 :=
      funext fun P => (comparison_const_formulas c P).1
    rw [h]
    exact continuousOn_const
  ·
    rw [(funext fun P => (comparison_const_formulas c P).2.1)]
    exact continuousOn_const
  ·
    rw [(funext fun P => (comparison_const_formulas c P).2.2.1)]
    exact continuousOn_const
  ·
    rw [(funext fun P => (comparison_const_formulas c P).2.2.2)]
    exact continuousOn_const

/-- The general forward kinetic operator annihilates constants. -/
theorem comparison_forwardOperator_const
    (A : FullKineticCoefficient d) (c : ℝ) (P : KineticPoint d) :
    forwardKineticOperator A (fun _  => c) P = 0 := by
  obtain ⟨ht,hx,_,hv⟩ := comparison_const_formulas c P
  rw [forwardKineticOperator_apply,ht,hx,hv]
  simp [PDE.vecDot, HypoellipticAleksandrov.matrixContraction]

/-- Restriction to a smaller set preserves the exact anisotropic classical class. -/
theorem comparison_regular_mono  {u : HypoellipticAleksandrov.KineticScalarField d}
    {D S : Set (KineticPoint d)} (hu : IsKineticC112On u D) (hSD : S ⊆ D) :
    IsKineticC112On u S :=
  ⟨hu.continuousOn.mono hSD,
    fun _ hp => hu.timeSlice_differentiableAt (hSD hp),
    fun _ hp => hu.positionSlice_contDiffAt (hSD hp),
    fun _ hp => hu.velocitySlice_contDiffAt (hSD hp),
    hu.continuousOn_kineticTimeDerivative.mono hSD,
    hu.continuousOn_kineticPositionGradient.mono hSD,
    hu.continuousOn_kineticVelocityGradient.mono hSD,
    hu.continuousOn_kineticVelocityHessian.mono hSD⟩

end HypoellipticAleksandrov.KineticAleksandrov
