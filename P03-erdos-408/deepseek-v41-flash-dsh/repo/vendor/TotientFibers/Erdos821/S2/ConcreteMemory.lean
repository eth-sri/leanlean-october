module

public import Erdos821.S2.MemoryIdentity
public import Erdos821.P3Live.Anchors
public import Erdos821.P3Live.SpanMemory
public import Erdos821.P3Span.LifespanClassification
public import Erdos821.P3Birth.SpanBirthTask
public import Erdos821.P3GW.SpanGhostWeight
public import Erdos821.P3Mark.SpanMarkWeight
public import Erdos821.P3Sum.SpanSumTask

/-! Instantiate all completed structural and local-weight leaves of the memory identity. -/

@[expose] public section

noncomputable section
namespace Erdos821.S2Core



theorem historyStructure_of_reconstruction (hRec : HistoryReconstructionTask) : HistoryStructureProofs :=
  ⟨SpanEdgeMemoryTask_proof, SpanBirthTask_proof, LifespanClassificationTask_proof,
    HistoryAnchorTask_proof, hRec⟩

end Erdos821.S2Core
