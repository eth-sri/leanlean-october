module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.MassRepresentation
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierCollar
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.MarginalRegularityScalar

/-! # Total mass of the actual ball exit measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo TheoremA Evolution

variable
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

section
variable (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})

/-- The actual ambient exit measure has mass one, by representation of the constant solution. -/
theorem ballExitRaw_mass :
    ballExitRaw hd B hB v₀ hR P T univ = 1 := by
  have hs : IsKineticC112On (fun _ : KineticPoint d => (1 : ℝ))
      (localStrip P.1.time T.1 v₀ R) :=
    isKineticC112On_of_contDiffOn (isOpen_localStrip _ _ _ _)
      contDiffOn_const
  have he : ∀ Q ∈ localStrip P.1.time T.1 v₀ R,
      forwardKineticOperator (ofTimeVelocityCoefficient B)
        (fun _ : KineticPoint d => (1 : ℝ)) Q = 0 := by
    intro Q _
    have hg : (fun v : PDE.Vec d => PDE.classicalGradient (fun _ => (1 : ℝ)) v) =
        fun _ => 0 := funext (_root_.HypoellipticAleksandrov.KineticAleksandrov.classicalGradient_const_eq_zero 1)
    have hv : kineticVelocityHessian (fun _ : KineticPoint d => (1 : ℝ)) Q = 0 := by
      unfold kineticVelocityHessian
      change (fun i j =>
        (fderiv ℝ (fun v => PDE.classicalGradient (fun _ => (1 : ℝ)) v)
          Q.velocity (PDE.basisVec i)) j) = 0
      rw [hg]
      have hf : fderiv ℝ (fun _ : PDE.Vec d => (0 : PDE.Vec d)) Q.velocity = 0 :=
        congrFun (fderiv_const (0 : PDE.Vec d)) Q.velocity
      rw [hf]
      rfl
    rw [forwardKineticOperator_apply, hv, matrixContraction_zero_right]
    simp [kineticTimeDerivative, kineticPositionGradient, PDE.vecDot]
  have hi := ballExit_represents hd B hB v₀ hR P T
    (fun _ => (1 : ℝ)) continuousOn_const hs
    ⟨1, fun _ _ => by simp⟩ he
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real] at hi
  exact (ENNReal.toReal_eq_one_iff _).mp hi.symm

/-- Centering preserves the unit mass of the actual exit measure. -/
theorem ballExit_mass :
    ballExit hd B hB v₀ hR P T univ = 1 := by
  unfold ballExit
  rw [Measure.map_apply (continuous_exitCoordinates _ _).measurable
    MeasurableSet.univ, preimage_univ]
  exact ballExitRaw_mass hd B hB v₀ hR P T

end

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
