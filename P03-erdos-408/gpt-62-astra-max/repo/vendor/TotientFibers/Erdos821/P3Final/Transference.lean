module

public import Erdos821.S2.ConcreteMemory
public import Erdos821.S2.ConcreteNorms
public import Erdos821.S2Nondiv.BigPrimeNondiv
public import Erdos821.S2.PacketAdapters
public import Erdos821.P3Rare.Proof
public import Erdos821.S2Empty.Final
public import Erdos821.P3High.Final
public import Erdos821.S2Full.FullMemoryNorm
public import Erdos821.S2Hist.HistoryReconstruction
public import Erdos821.S2Resid.ResidueFactorization
public import Erdos821.P3Phys.PhysicalPathExpansion
public import Erdos821.S2Root.AbsoluteClosedRootProof
public import Erdos821.P3.ResidueReplacement
public import Erdos821.S2Packet.AbsolutePhysicalPacket
public import Erdos821.S2Ltrans.TransferenceAssembly

/-! The memory and path estimates used by local transference. -/

@[expose] public section

namespace Erdos821.P3Final

open Erdos821.S2Core

/-- Assemble exactly the proofs used by the local transference theorem. -/
theorem memoryProofs : MemoryTransferenceProofs where
  ghostParameters := S2Gpar.GhostAnalyticParametersTask_proof
  emptyBoundary := S2Empty.EmptyBoundaryMassTask_proof
  nondiv := S2Nondiv.BigPrimeNondivTask_proof
  absoluteEdge := MemoryEdgeAbsoluteTask_proof
  fullMemory F r := concrete_full_memory_estimate F r S2Empty.EmptyBoundaryMassTask_proof
    (MemoryRareTask_proof F r) (HighRankMemoryTask_proof F r) (S2Full.FullMemoryNormTask_proof F r)
  structureProofs := historyStructure_of_reconstruction S2Hist.HistoryReconstructionTask_proof
  ghostWeights := P3Gw.SpanGhostWeightTask_proof
  markWeights := P3Mark.SpanMarkWeightTask_proof
  spanSum := SpanSumTask_proof
  residues := S2Resid.residueFactorizationTask_proof
  physicalPaths := PhysicalPathExpansionTask_proof
  absoluteRoot := S2Root.AbsoluteClosedRootTask_proof
  crt := @P3Core.uniform_residue_replacement_proof

end Erdos821.P3Final
