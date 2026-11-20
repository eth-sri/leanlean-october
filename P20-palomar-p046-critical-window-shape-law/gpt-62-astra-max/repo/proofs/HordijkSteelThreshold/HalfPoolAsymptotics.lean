module

public import proofs.HordijkSteelThreshold.FixedPoolReactionLaw

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF.Polymer RAF.Concrete unitInterval
open scoped Topology

noncomputable def halfCatalystPool (n : ℕ) : Finset (Molecule n) :=
  finiteInitialSegment (Molecule n) (Fintype.card (Molecule n)/2)

@[simp] theorem halfCatalystPool_card (n : ℕ) :
    (halfCatalystPool n).card = Fintype.card (Molecule n)/2 :=
  card_finiteInitialSegment _ _ (Nat.div_le_self _ _)

end HordijkSteelThreshold
