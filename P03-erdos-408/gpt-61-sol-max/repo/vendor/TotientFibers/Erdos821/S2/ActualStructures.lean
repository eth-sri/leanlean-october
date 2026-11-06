module

public import Erdos821.S2.ConfigurationSum
public import Erdos821.P3Live.Anchors
public import Erdos821.P3Live.SpanMemory

/-! Instantiate the accepted anchor and inverse edge-memory proofs. -/

@[expose] public section

section
namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

namespace ResiduePath

variable {F : FixedData} {P : PrimeGroups} {J m n : ℕ} {A : Model F P J m}
  (Q : ResiduePath A n)

theorem reconstructedHistory_valid_of_lifespans  S 
    (hq : Q.Valid)  hS 
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
     y  (hy : Q.SmallCompatible y) :
    (Q.reconstructedHistory S hS y).Valid :=
  Q.reconstructedHistory_valid SpanEdgeMemoryTask_proof S hq hS hk y hy

end ResiduePath

end Erdos821.S2Core
