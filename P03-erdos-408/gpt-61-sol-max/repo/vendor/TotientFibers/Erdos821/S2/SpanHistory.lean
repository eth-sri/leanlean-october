module
public import Mathlib.Tactic

public import Erdos821.S2.SpanEdgeValidity

/-! A literal history reconstructed from a residue path and prime lifespans. -/

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

namespace ResiduePath

variable {A : Model F P J m} {n : ℕ} (Q : ResiduePath A n)

def reconstructedHistory (S : LifespanAssignment P n) (hS : Q.lifespanValid S)
    (y : P.SmallResidues) : MemoryHistory A n where
  before := Q.stateBefore S y
  after := Q.stateAfter S y
  ghost := Q.reconstructedGhostChoice S hS y
  edge := fun i => ⟨Q.sourcePerm i, Q.targetPerm i, Q.pattern i, Q.free i,
    Q.reconstructedTransferChoice S y i⟩

theorem reconstructedHistory_valid (hMem : SpanEdgeMemoryTask)
     S  (hq : Q.Valid)  hS 
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
     y  (hy : Q.SmallCompatible y) :
    (Q.reconstructedHistory S hS y).Valid := ⟨Erdos821.S2Core.ResiduePath.memoryBefore_zero Q S, ⟨Erdos821.S2Core.ResiduePath.memoryAfter_last Q S, ⟨fun i => ⟨rfl, ⟨rfl, Erdos821.S2Core.ResiduePath.reconstructedGhostChoice_valid Q S hS y i⟩⟩, fun i => ⟨Erdos821.S2Core.ResiduePath.reconstructedTransferChoice_valid Q hMem S hq hS hk y hy i, trivial⟩⟩⟩⟩

theorem reconstructedHistory_projection  S 
     hS   y  :
    (Q.reconstructedHistory S hS y).toResiduePath = Q := by
  cases Q
  rfl


end ResiduePath
end Erdos821.S2Core
