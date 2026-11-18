module

public import Erdos821.Blueprint.Graph

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

inductive TransferMode where
  | all
  | clean
  | dirty
  deriving DecidableEq




def permuteActive {M : ℕ} (π : P.Permutations M) (s : P.MemoryState M) : P.MemoryState M :=
  (s.1, P.act π s.2.1, s.2.2)




















end Erdos821.Blueprint.Graph
