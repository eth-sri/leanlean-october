module

public import Erdos821.S2.MemoryEdge

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

lemma visitQ_pos  q  (hq0 : 0 < q)  n   i  :
    0 < visitQ q n i := by
  unfold visitQ
  split
  · exact Real.sqrt_pos.mpr hq0
  · exact hq0

lemma eta_lt_one  F   n   i  : eta F n i < 1 := by
  unfold eta
  have h := visitQ_pos F.q F.q_pos n i
  linarith

end Erdos821.P3Edge
