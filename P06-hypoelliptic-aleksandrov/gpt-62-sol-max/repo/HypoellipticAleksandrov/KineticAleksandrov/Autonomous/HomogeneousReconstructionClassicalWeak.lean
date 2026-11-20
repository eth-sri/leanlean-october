module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PhysicalJets
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionSource
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReconstructionTraces

/-! # Weak forcing of physical C112 tests

The forcing is the literal scalar kinetic operator. The directional-jet identity
discharges the weak equation without requiring extra transported derivatives.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Evolution SectionTwo MeasureTheory Set

/-- A physical C112 test satisfies its actual weak equation in packed coordinates. -/
theorem reconstruction_test_isWeakTransportedSolution {lam Lam : ℝ}
    (A : SmoothAutonomous lam Lam) {D : Set Point} (hD : IsOpen D)
    {phi : Point → ℝ} (hphi : IsKineticC112On phi D) :
    IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1)
      (packedPhysicalPoint ⁻¹' D) (phi ∘ packedPhysicalPoint)
      (forwardScalarOperator A.a phi ∘ packedPhysicalPoint) := by
  simpa only [Function.comp_def, forwardKineticOperator_apply, forwardScalarOperator, PDE.vecDot, matrixContraction,
    Fin.sum_univ_one, evolutionCoefficient] using
    packedPhysicalPoint_classical_weak (evolutionCoefficient A.a) (evolutionCoefficient_smooth A)
      (evolutionCoefficient_symmetric A.a) hD hphi

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
