module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomyBoundedData
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdapters
import Aesop



/-! # Physical-coordinate generator of the full-space autonomous action -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- Exchange position and velocity, and reverse terminal time into elapsed time. -/
def autonomousReversal (p : Point) : Point := ⟨-p.time, p.velocity, p.position⟩

/-- The generator equation uses positive transport and diffusion on its right side. -/
def autonomousGeneratorResidual (a : ℝ → ℝ → ℝ) (u : Point → ℝ) (p : Point) : ℝ :=
  kineticTimeDerivative u p - p.velocity 0 * kineticPositionGradient u p 0 -
    a (p.position 0) (p.velocity 0) * kineticVelocityHessian u p 0 0

/-- Reflect physical position without changing elapsed time or velocity. -/
def autonomousPositionReflection (p : Point) : Point :=
  ⟨p.time, -p.position, p.velocity⟩

variable (a : ℝ → ℝ → ℝ) (u : Point → ℝ) (p : Point)

/-- Position reflection converts the generator equation to the source PDE convention. -/
theorem autonomous_generator_positionReflection  :
    autonomousScalarOperator (reflectedAutonomous a) (u ∘ autonomousPositionReflection) p =
      autonomousGeneratorResidual a u (autonomousPositionReflection p) := by
  have hg : kineticPositionGradient (u ∘ autonomousPositionReflection) p =
      -kineticPositionGradient u (autonomousPositionReflection p) := by
    ext i
    let f  := fun x => u ⟨p.time, x, p.velocity⟩
    let e := ContinuousLinearEquiv.neg ℝ (M := PDE.Vec 1)
    change (fderiv ℝ (f ∘ e) p.position) (PDE.basisVec i) =
      -(fderiv ℝ f (-p.position)) (PDE.basisVec i)
    rw [e.comp_right_fderiv]
    simp [e]
  aesop

/-- The time and coordinate exchange gives the source generator with its literal sign. -/
theorem autonomous_generator_reversal  :
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

/-- Physical terminal data use position first, velocity second. -/
def physicalTerminalDatum (F : BoundedBorel (EvolutionAmbientState 1)) :
    BoundedBorel (EvolutionAmbientState 1) :=
  F.pullback Prod.swap measurable_swap

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
