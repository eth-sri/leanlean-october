module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Autonomy
import Mathlib.Basic.NNReal.Basic

/-! # The full-space autonomous semigroup on every bounded Borel function -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- Insert an ambient state into the unrestricted full-space fiber. -/
def fullspaceState (t : ℝ) (x : EvolutionAmbientState 1) :
    EvolutionState autonomousWholeDomain (fun _ => 0) t :=
  ⟨x, by rw [autonomous_stateSet]; trivial⟩

/-- State insertion is measurable. -/
theorem measurable_fullspaceState (t : ℝ) : Measurable (fullspaceState t) :=
  measurable_id.subtype_mk

/-- The autonomous full-space operator at a nonnegative elapsed time. -/
def fullSpaceSemigroup (E : FullSpaceEvolution) (t : NNReal) :
    BoundedBorel (EvolutionState autonomousWholeDomain (fun _ => 0) 0) →ₗ[ℝ]
      BoundedBorel (EvolutionState autonomousWholeDomain (fun _ => 0) 0) :=
  E.1 0 t t.coe_nonneg

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
