module

public import proofs.HordijkSteelThreshold.CatalystPoolBlocks

@[expose] public section

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory
open RAF RAF.Polymer RAF.Concrete

/-- Coordinate block queried by a finite family of reactions against a fixed
prospective catalyst pool. -/
def catalystPoolFamilyBlock {n : Nat} (C : Finset (Molecule n))
    (R : Finset (Reaction n)) : Finset (AmbientCoord n) :=
  C.product R

/-- At least one reaction in a finite family is catalyzed by the prospective
internal pool. -/
def catalystPoolFamilyOpen {n : Nat} (ω : AmbientCoord n → Prop)
    (C : Finset (Molecule n)) (R : Finset (Reaction n)) : Prop :=
  ∃ r ∈ R, catalystPoolOpen ω C r

theorem catalystPoolFamilyBlock_disjoint {n : Nat}
    (C : Finset (Molecule n)) {R S : Finset (Reaction n)}
    (hRS : Disjoint R S) :
    Disjoint (catalystPoolFamilyBlock C R)
      (catalystPoolFamilyBlock C S) := by
  rw [Finset.disjoint_left]
  intro z hzR hzS
  have hrR := (Finset.mem_product.mp hzR).2
  have hrS := (Finset.mem_product.mp hzS).2
  exact Finset.disjoint_left.mp hRS hrR hrS

end HordijkSteelThreshold
