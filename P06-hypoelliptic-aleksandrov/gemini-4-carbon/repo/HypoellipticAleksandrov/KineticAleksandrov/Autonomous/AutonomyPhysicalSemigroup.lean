module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Autonomy
import Mathlib.Basic.NNReal.Basic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomyAction

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

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


/-- The coordinate exchange is an actual linear equivalence of bounded Borel carriers. -/
def physicalBorelEquiv : BoundedBorel (EvolutionAmbientState 1) ≃ₗ[ℝ]
    BoundedBorel (EvolutionState autonomousWholeDomain (fun _ => 0) 0) where
  toFun F := terminalStateDatum (physicalTerminalDatum F)
  invFun G := G.pullback (fun x => fullspaceState 0 x.swap)
    ((measurable_fullspaceState 0).comp measurable_swap)
  left_inv F := by apply BoundedBorel.ext; intro x; rfl
  right_inv G := by apply BoundedBorel.ext; intro x; rfl
  map_add' F G := by apply BoundedBorel.ext; intro x; rfl
  map_smul' c F := by apply BoundedBorel.ext; intro x; rfl

/-- The same supplied semigroup, conjugated to physical state order `(X,v)`. -/
def fullSpacePhysicalSemigroup (E : FullSpaceEvolution) (t : NNReal) :
    BoundedBorel (EvolutionAmbientState 1) →ₗ[ℝ] BoundedBorel (EvolutionAmbientState 1) :=
  physicalBorelEquiv.symm.toLinearMap.comp
    ((fullSpaceSemigroup E t).comp physicalBorelEquiv.toLinearMap)

/-- The physical semigroup and the literal kernel action are the same function. -/
theorem fullSpacePhysicalSemigroup_eq_action {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (t : NNReal) (F : BoundedBorel (EvolutionAmbientState 1)) (x : EvolutionAmbientState 1) :
    fullSpacePhysicalSemigroup E t F x = fullSpaceAction E F ⟨t, x.1, x.2⟩ := by
  rw [fullSpaceAction_eq_zeroTime A E hE F _ t.coe_nonneg]
  let p := fullspaceState 0 x.swap
  exact (hE.2.1 0 t t.coe_nonneg p (terminalStateDatum (physicalTerminalDatum F))).trans
    (integral_master_eq_fiber E.2 autonomousWholeDomain_measurable 0 t t.coe_nonneg p
      (physicalTerminalDatum F) (physicalTerminalDatum F).measurable).symm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

