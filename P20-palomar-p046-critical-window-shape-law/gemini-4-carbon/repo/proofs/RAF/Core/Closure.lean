module

public import proofs.RAF.Core.CRS

@[expose] public section

namespace RAF

variable {M R : Type*} [DecidableEq M]

def Enabled (Q : CRS M R) (available : Finset M) (r : R) : Prop :=
  Q.inputs r ⊆ available

instance enabledDecidable (Q : CRS M R) (available : Finset M) (r : R) :
    Decidable (Enabled Q available r) := by
  unfold Enabled
  infer_instance

def closureStep (Q : CRS M R) (S : Finset R) (available : Finset M) : Finset M :=
  available ∪ S.biUnion (fun r => if Enabled Q available r then Q.outputs r else ∅)

def closureAt (Q : CRS M R) (S : Finset R) : Nat → Finset M
  | 0 => Q.food
  | k + 1 => closureStep Q S (closureAt Q S k)

end RAF
