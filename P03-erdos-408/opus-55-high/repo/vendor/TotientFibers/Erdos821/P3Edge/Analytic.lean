module

public import Erdos821.S2.MemoryEdge

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph

lemma visitQ_pos (q : ℝ) (hq0 : 0 < q) (n : ℕ) (i : Fin (n + 1)) :
    0 < visitQ q n i := by
  unfold visitQ
  positivity

lemma eta_lt_one (F : FixedData) (n : ℕ) (i : Fin (n + 1)) : eta F n i < 1 := by
  unfold eta
  have h := visitQ_pos F.q F.q_pos n i
  linarith

end Erdos821.P3Edge
