module

public import proofs.RAFReactionQuotient.QuotientMap

@[expose] public section

namespace RAFReactionQuotient
open Classical RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

def liftMolecule {n N : ℕ} (h : n ≤ N) (x : Molecule n) : Molecule N :=
  ⟨⟨x.1.val, lt_of_lt_of_le x.1.isLt h⟩, x.2⟩

@[simp] theorem liftMolecule_length {n N : ℕ} (h : n ≤ N) (x : Molecule n) :
    molLength (liftMolecule h x) = molLength x := rfl

end RAFReactionQuotient
