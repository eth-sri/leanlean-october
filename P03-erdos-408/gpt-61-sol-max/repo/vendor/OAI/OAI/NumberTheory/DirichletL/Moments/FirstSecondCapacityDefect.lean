module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.FirstSecondCapacityShift

@[expose] public section

namespace OAI


open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstSecondCapacityLedger
open CenteredMomentAllocatedChildCapacity CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentEligibleEnergy CenteredMomentLiveCapacity
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

variable {ι:Type*}[Fintype ι][DecidableEq ι]

lemma width_defect_cost (x B δ:ℝ)(hB:0≤B)(hδ:0≤δ)(hx:x≤δ):
    x+max (B-x) 0/6≤δ+B/6 := by
  grind

end SevenEighths.CenteredMomentFirstSecondCapacityLedger



end OAI
