module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomyBoundedData
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdapters

/-! # Physical-coordinate generator of the full-space autonomous action -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

section
variable (a : ℝ → ℝ → ℝ) (u : Point → ℝ) (p : Point)

include p in
/-- Exchange position and velocity, and reverse terminal time into elapsed time. -/
def autonomousReversal : Point := ⟨-p.time, p.velocity, p.position⟩

include a u p in
/-- The generator equation uses positive transport and diffusion on its right side. -/
def autonomousGeneratorResidual : ℝ :=
  kineticTimeDerivative u p - p.velocity 0 * kineticPositionGradient u p 0 -
    a (p.position 0) (p.velocity 0) * kineticVelocityHessian u p 0 0

include p in
/-- Reflect physical position without changing elapsed time or velocity. -/
def autonomousPositionReflection : Point :=
  ⟨p.time, -p.position, p.velocity⟩

/-- Position reflection converts the generator equation to the source PDE convention. -/
theorem autonomous_generator_positionReflection :
    autonomousScalarOperator (reflectedAutonomous a) (u ∘ autonomousPositionReflection) p =
      autonomousGeneratorResidual a u (autonomousPositionReflection p) := by
  have hg : kineticPositionGradient (u ∘ autonomousPositionReflection) p =
      -kineticPositionGradient u (autonomousPositionReflection p) := by
    ext i
    let f := fun x => u ⟨p.time, x, p.velocity⟩
    let e := ContinuousLinearEquiv.neg ℝ (M := PDE.Vec 1)
    change (fderiv ℝ (f ∘ e) p.position) (PDE.basisVec i) =
      -(fderiv ℝ f (-p.position)) (PDE.basisVec i)
    rw [e.comp_right_fderiv]
    simp [e]
  rw [autonomousScalarOperator, autonomousGeneratorResidual, hg]
  change kineticTimeDerivative u (autonomousPositionReflection p) +
      p.velocity 0 * (-kineticPositionGradient u (autonomousPositionReflection p) 0) -
      a (-p.position 0) (p.velocity 0) *
        kineticVelocityHessian u (autonomousPositionReflection p) 0 0 = _
  dsimp only [autonomousPositionReflection, Pi.neg_apply]
  ring

/-- The time and coordinate exchange gives the source generator with its literal sign. -/
theorem autonomous_generator_reversal :
    autonomousGeneratorResidual a (u ∘ autonomousReversal) p =
      -transportedForwardOperator (evolutionCoefficient a) (identityDrift 1) u
        (autonomousReversal p) := by
  rw [autonomousGeneratorResidual, transportedForwardOperator_apply]
  have ht : kineticTimeDerivative (u ∘ autonomousReversal) p =
      -kineticTimeDerivative u (autonomousReversal p) :=
    deriv_comp_neg (fun r => u ⟨r, p.velocity, p.position⟩) p.time
  rw [ht]
  simp only [matrixContraction, Fin.sum_univ_one, fullKineticCoefficientAt,
    evolutionCoefficient, PDE.vecDot, identityDrift]
  change -kineticTimeDerivative u (autonomousReversal p) -
      p.velocity 0 * kineticVelocityGradient u (autonomousReversal p) 0 -
      a (p.position 0) (p.velocity 0) * diffusedHessian u (autonomousReversal p) 0 0 = _
  dsimp only [autonomousReversal, id_eq]
  ring

end

/-- Physical terminal data use position first, velocity second. -/
def physicalTerminalDatum (F : BoundedBorel (EvolutionAmbientState 1)) :
    BoundedBorel (EvolutionAmbientState 1) :=
  F.pullback Prod.swap measurable_swap

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
