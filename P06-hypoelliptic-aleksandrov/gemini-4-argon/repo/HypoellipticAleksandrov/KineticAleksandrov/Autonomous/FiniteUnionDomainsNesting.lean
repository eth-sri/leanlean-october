module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsBoundary

/-! # Internal velocity faces and the exact terminal/lateral boundary split -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/- The internal restart boundary uses strict physical time and the larger open velocity set. -/
def finiteUnionInternalExit (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ) : Set Point :=
  {p | sMinus < p.time ∧ p.time < T ∧
    p.velocity 0 ∈ frontier H1.carrier ∩ H2.carrier}

/- The internal restart boundary is part of the smaller strip's prescribed exit. -/
theorem finiteUnionInternalExit_subset_exit (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ) :
    finiteUnionInternalExit H1 H2 sMinus T ⊆ finiteUnionExitSet H1 sMinus T :=
  fun _ hp => Or.inr ⟨hp.1, hp.2.1, hp.2.2.1⟩

/- The smaller exit is exactly the outer exit part plus the internal restart part. -/
theorem measurableSet_finiteUnionInternalExit (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ) :
    MeasurableSet (finiteUnionInternalExit H1 H2 sMinus T) := by
  unfold finiteUnionInternalExit
  convert ((isOpen_lt continuous_const continuous_time).measurableSet.inter
    (isOpen_lt continuous_time continuous_const).measurableSet).inter
    ((isClosed_frontier.measurableSet.inter H2.isOpen_carrier.measurableSet).preimage
      (((continuous_apply 0).comp continuous_velocity).measurable)) using 1
  ext p
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, Function.comp_apply]
  tauto

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
