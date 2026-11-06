module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.MassRepresentation
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierCollar

/-! # Total mass of the actual ball exit measure -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo TheoremA Evolution

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

variable (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})

/-- The actual ambient exit measure has mass one, by representation of the constant solution. -/
theorem ballExitRaw_mass  :
    ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T univ = 1 := by
  have hs : IsKineticC112On (fun _ : KineticPoint d => (1))
      (localStrip P.1.time T.1 v₀ R) :=
    isKineticC112On_of_contDiffOn (isOpen_localStrip _ _ _ _)
      contDiffOn_const
  have he : ∀ Q ∈ localStrip P.1.time T.1 v₀ R,
      forwardKineticOperator (ofTimeVelocityCoefficient B)
        (fun _ : KineticPoint d => (1)) Q = 0 := by
    intro Q _
    have hg : (fun v : PDE.Vec d => PDE.classicalGradient _ v) =
        fun _ => 0 := funext (classicalGradient_const 1)
    have hv : kineticVelocityHessian (fun _ : KineticPoint d => (1)) Q = 0 := by
      unfold kineticVelocityHessian
      aesop
    rw [forwardKineticOperator_apply, hv]
    simp [kineticTimeDerivative, kineticPositionGradient, PDE.vecDot]
  have hi := ballExit_represents hH hLE hd hlam hLam B hB v₀ hR P T
    _ continuousOn_const hs
    ⟨1, fun _ _ => by simp⟩ he
  simp only [integral_const, smul_eq_mul, mul_one] at hi
  exact (ENNReal.toReal_eq_one_iff _).mp hi.symm

/-- Centering preserves the unit mass of the actual exit measure. -/
theorem ballExit_mass  :
    ballExit hH hLE hd hlam hLam B hB v₀ hR P T univ = 1 := by
  unfold ballExit
  rw [Measure.map_apply (continuous_exitCoordinates _ _).measurable
    MeasurableSet.univ]
  exact ballExitRaw_mass hH hLE hd hlam hLam B hB v₀ hR P T

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
