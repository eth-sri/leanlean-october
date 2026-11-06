module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ReflectionAPI

/-! # Slice-calculus identities for the kinetic reflection -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open Set
open HypoellipticAleksandrov.Parabolic

variable {d : ℕ}

variable (u : HypoellipticAleksandrov.KineticScalarField d) (P : KineticPoint d)

/-- Time differentiation under reflection reverses sign, including total derivative values. -/
theorem kineticTimeDerivative_reflection   :
    kineticTimeDerivative (u ∘ kineticReflection) P =
      -kineticTimeDerivative u (kineticReflection P) := deriv_comp_neg (fun r  => u ⟨r, -P.position, P.velocity⟩) P.time

/-- Position differentiation under reflection reverses sign. -/
theorem kineticPositionGradient_reflection   :
    kineticPositionGradient (u ∘ kineticReflection) P =
      -kineticPositionGradient u (kineticReflection P) := by
  ext i
  let f  := fun x => u ⟨-P.time,x,P.velocity⟩
  let e := ContinuousLinearEquiv.neg ℝ (M := PDE.Vec d)
  change (fderiv ℝ (f ∘ e) P.position) (PDE.basisVec i) =
    -(fderiv ℝ f (-P.position)) (PDE.basisVec i)
  rw [e.comp_right_fderiv]
  simp [e]

/-- The unchanged velocity coordinate leaves the velocity Hessian unchanged. -/
theorem kineticVelocityHessian_reflection   :
    kineticVelocityHessian (u ∘ kineticReflection) P =
      kineticVelocityHessian u (kineticReflection P) := rfl

/-- Reflection reverses the operator, including the total derivative evaluator convention. -/
theorem reflectedKineticOperator_reflection
    (A : CoefficientField d) (u : HypoellipticAleksandrov.KineticScalarField d) (P : KineticPoint d) :
    forwardKineticOperator (ofTimeVelocityCoefficient (kineticReflectedCoefficient A))
        (u ∘ kineticReflection) P =
      -backwardOperatorOfTimeVelocityCoefficient A u (kineticReflection P) := by
  rw [forwardKineticOperator_apply, backwardOperatorOfTimeVelocityCoefficient_apply,
    kineticTimeDerivative_reflection, kineticPositionGradient_reflection,
    kineticVelocityHessian_reflection]
  simp only [ofTimeVelocityCoefficient, kineticReflectedCoefficient, kineticReflection]
  have hdot : PDE.vecDot P.velocity (-kineticPositionGradient u (kineticReflection P)) =
      -PDE.vecDot P.velocity (kineticPositionGradient u (kineticReflection P)) := by
    simp [PDE.vecDot, Finset.sum_neg_distrib]
  simp only [kineticReflection] at hdot
  rw [hdot]
  ring

/-- Anisotropic regularity is preserved by source reflection on any domain. -/
theorem isKineticC112On_kineticReflection
    (u : HypoellipticAleksandrov.KineticScalarField d) (D : Set (KineticPoint d))
    (hu : IsKineticC112On u D) :
    IsKineticC112On (u ∘ kineticReflection) (kineticReflection ⁻¹' D) := by
  rcases hu with ⟨hc,ht,hx,hv,hct,hcx,hcv,hch⟩
  have hR : ContinuousOn (kineticReflection (d := d)) (kineticReflection ⁻¹' D) :=
    (continuous_kineticReflection d).continuousOn
  have hm : MapsTo (kineticReflection (d := d)) (kineticReflection ⁻¹' D) D :=
    fun _ h => h
  refine ⟨hc.comp hR hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hP
    exact (ht _ hP).comp P.time differentiableAt_id.neg
  · intro P hP
    change ContDiffAt ℝ 1 (fun x  => u ⟨-P.time, -x, P.velocity⟩) P.position
    have hf : ContDiffAt ℝ 1 (fun x  => u ⟨-P.time, x, P.velocity⟩)
        (-P.position) := hx (kineticReflection P) hP
    exact hf.comp P.position
      (contDiffAt_id.neg )
  · intro P hP
    exact hv _ hP
  · rw [show kineticTimeDerivative (u ∘ kineticReflection) =
        fun P => -kineticTimeDerivative u (kineticReflection P) from
          funext (kineticTimeDerivative_reflection u)]
    exact (hct.comp hR hm).neg
  · rw [show kineticPositionGradient (u ∘ kineticReflection) =
        fun P => -kineticPositionGradient u (kineticReflection P) from
          funext (kineticPositionGradient_reflection u)]
    exact (hcx.comp hR hm).neg
  · exact hcv.comp hR hm
  · exact hch.comp hR hm

end HypoellipticAleksandrov.KineticAleksandrov
