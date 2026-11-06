module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-! # The measure-preserving coordinate chart for native spatial weak jets -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory

/-- The standard coordinate permutation separates position and velocity coordinates. -/
def spatialCoordinateCLE (d : ℕ) : PDE.Vec (d + d) ≃L[ℝ] XV d :=
  ((LinearEquiv.piCongrLeft ℝ (fun _ : Fin (d + d) => ℝ) finSumFinEquiv).symm.trans
    (LinearEquiv.sumPiEquivProdPi ℝ (Fin d) (Fin d) (fun _ => ℝ))).toContinuousLinearEquiv

/-- The measurable coordinate permutation with the same underlying map. -/
def spatialCoordinateMeasurableEquiv (d : ℕ) : PDE.Vec (d + d) ≃ᵐ XV d :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (d + d) => ℝ) finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin d ⊕ Fin d => ℝ))

variable (d : ℕ)

/-- The topological and measurable spatial charts agree exactly. -/
theorem spatialCoordinateMeasurableEquiv_apply  (x : PDE.Vec (d + d)) :
    spatialCoordinateMeasurableEquiv d x = spatialCoordinateCLE d x := rfl

/-- This coordinate chart preserves the native product Lebesgue measure. -/
theorem measurePreserving_spatialCoordinate  :
    MeasurePreserving (spatialCoordinateMeasurableEquiv d) volume volume :=
  ((volume_measurePreserving_piCongrLeft _
    finSumFinEquiv).symm).trans
    (volume_measurePreserving_sumPiEquivProdPi _)

/-- Position basis directions are unchanged by unpacking. -/
theorem spatialCoordinate_basis_position {d : ℕ} (i : Fin d) :
    spatialCoordinateCLE d (PDE.basisVec (Fin.castAdd d i)) = (PDE.basisVec i, 0) := by
  ext j
  all_goals have hj := j.isLt
  all_goals simp [spatialCoordinateCLE, PDE.basisVec, LinearEquiv.piCongrLeft,
    LinearEquiv.piCongrLeft', LinearEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi,
    Equiv.piCongrLeft', finSumFinEquiv, Pi.single_apply, Fin.ext_iff]
  all_goals grind

/-- Velocity basis directions are unchanged by unpacking. -/
theorem spatialCoordinate_basis_velocity {d : ℕ} (i : Fin d) :
    spatialCoordinateCLE d (PDE.basisVec (Fin.natAdd d i)) = (0, PDE.basisVec i) := by
  ext j
  all_goals have hj := j.isLt
  all_goals simp [spatialCoordinateCLE, LinearEquiv.piCongrLeft, Pi.single_apply, Fin.ext_iff]
  omega

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
