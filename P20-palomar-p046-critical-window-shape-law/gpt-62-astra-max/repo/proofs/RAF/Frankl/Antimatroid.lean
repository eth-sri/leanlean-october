module

public import proofs.RAF.Frankl.Semantics

@[expose] public section

namespace RAF.Frankl

open RAF

variable {M R : Type*} [DecidableEq M]

@[simp] theorem foodGenerated_empty (Q : CRS M R) :
    FoodGenerated Q (∅ : Finset R) := by
  intro r hr
  simp at hr

end RAF.Frankl
