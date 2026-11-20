module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.DeterministicBoxOccupationMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsSpatialC2

/-! # The physical coordinate equivalence for compact spatial Green tests -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic SectionTwo Evolution MeasureTheory Set

/-- The physical position-velocity order is the swapped native scalar order. -/
def physicalStateCLE : EvolutionAmbientState 1 ≃L[ℝ] Z :=
  (PDE.scalarToVecOneContinuousLinearEquiv.symm.prodCongr
    PDE.scalarToVecOneContinuousLinearEquiv.symm).trans
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)

variable (a : ℝ → ℝ → ℝ) (f : Z → ℝ) (p : Point) (hf : Continuous f) (hc : HasCompactSupport f)

include a f in
/-- The physical scalar spatial generator, with the source sign and coordinate convention. -/
def physicalSpatialOperator (z : Z) : ℝ :=
  z.2 * deriv (fun X => f (X, z.2)) z.1 +
    a z.1 z.2 * deriv (deriv (fun v => f (z.1, v))) z.2

/-- The physical spatial generator agrees with the established physical operator. -/
theorem physicalSpatialOperator_eq_forward :
    physicalSpatialOperator a f (p.position 0, p.velocity 0) =
      forwardScalarOperator a (fun q => f (q.position 0, q.velocity 0)) p := by
  rw [forwardScalarOperator, kineticPositionGradient_scalar,
    kineticVelocityHessian_scalar]
  have ht : kineticTimeDerivative (fun q : Point => f (q.position 0, q.velocity 0)) p = 0 := by
    change deriv (fun _ : ℝ => f (p.position 0, p.velocity 0)) p.time = 0
    apply deriv_const
  rw [ht]
  dsimp only [physicalSpatialOperator]
  ring

/-- Native compact spatial tests have exactly the physical generator after coordinate exchange. -/
theorem physicalSpatialOperator_eq_native :
    transportedForwardOperator (evolutionCoefficient a) (identityDrift 1)
      (fun q => f (nativeToXV (q.position, q.velocity))) p =
      physicalSpatialOperator a f (p.velocity 0, p.position 0) := (terminalPhysicalPoint_operator a
    (fun q => f (q.position 0, q.velocity 0)) p).trans
      (physicalSpatialOperator_eq_forward a f (terminalPhysicalPoint p)).symm

include hf hc in
/-- A physical compact C² spatial test gives a native bounded Borel terminal datum. -/
def physicalCompactDatum :
    BoundedBorel (EvolutionAmbientState 1) := by
  let C := (hf.bounded_above_of_compact_support hc).choose
  have hb := (hf.bounded_above_of_compact_support hc).choose_spec
  refine ⟨f ∘ nativeToXV, hf.measurable.comp nativeToXV_measurable,
    max C 0, le_max_right _ _, fun x => ?_⟩
  have hh : |f (nativeToXV x)| ≤ C := by
    simpa only [Real.norm_eq_abs] using hb (nativeToXV x)
  exact hh.trans (le_max_left _ _)

/-- Compact physical C² tests retain native joint regularity. -/
theorem physicalCompactDatum_contDiff (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) : ContDiff ℝ 2 (physicalCompactDatum f hf.continuous hc) := by
  exact hf.comp physicalStateCLE.contDiff

/-- Compact physical support remains compact under the native coordinate equivalence. -/
theorem physicalCompactDatum_hasCompactSupport : HasCompactSupport (physicalCompactDatum f hf hc) := by
  exact hc.comp_homeomorph physicalStateCLE.toHomeomorph

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
