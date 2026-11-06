module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackCorridorsInclusions
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackCorridorsRegion
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackCorridorsGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Holder.SkeletonApproximation
import Mathlib.Tactic

/-! # Source stack corridors for the common growth-lemma witnesses

The comparison region depends only on dimension and stack height. The path is Hermite
on the travel interval and tangent before its initial time, as in the companion paper.
-/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
open Set

/- Exact source cap and comparison-region corridors for every stack endpoint. -/
theorem stackComparisonRegion_geometry (d m : ℕ) :
    IsOpen (stackComparisonRegion d m) ∧ Bornology.IsBounded (stackComparisonRegion d m) ∧
      closure (backwardCylinder (⟨0,0,0⟩ : KineticPoint d) 1) ⊆ stackComparisonRegion d m ∧
      closure (forwardStack (⟨0,0,0⟩ : KineticPoint d) 1 m) ⊆
        stackComparisonRegion d m :=
  ⟨isOpen_stackComparisonRegion d m, isBounded_stackComparisonRegion d m,
    closure_unitCylinder_subset_comparison d m, closure_unitStack_subset_comparison d m⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
