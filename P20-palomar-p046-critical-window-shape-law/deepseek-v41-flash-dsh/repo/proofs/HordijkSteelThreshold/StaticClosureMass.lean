module

public import proofs.HordijkSteelThreshold.WordEffectiveClosure

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval Filter
open scoped Topology ENNReal

/-- The effective-component estimate transferred to actual ordinary reversible
closure. The universe cardinality is the literal source molecule count. -/
theorem measure_temporaryClosure_deficit {L N w k : ℕ} (hL : 2*w ≤ L)
    (hk : 5*k ≤ w) (hfood : 0 < L) (hN : 0 < N) (a : I) (d : ℕ) (hd : 0 < d) :
    staticReactionMeasure N a {ω |
      (temporaryReactionClosure L (staticOpenReactions ω)).card+d ≤ Fintype.card (Molecule N)} ≤
      contourBudget a k/(1-contourBudget a k) +
      (Fintype.card (Molecule N) : ENNReal)*(contourBudget a k/(1-contourBudget a k))/d := by
  have hcard : Fintype.card (Molecule N) = (actualBinaryWords N).card := by
    rw [card_molecules_exact, actualBinaryWords_card]
  rw [hcard]
  calc
    _ ≤ staticReactionMeasure N a {ω | (rootedMolecularWords hL ω).card+d ≤
        (actualBinaryWords N).card} := by
      apply measure_mono
      intro ω hω
      have hh := rootedMolecularWords_card_le_closure hL ω
      exact Nat.le_trans (Nat.add_le_add_right hh d) hω
    _ ≤ _ := measure_rootedMolecularWords_deficit hL hk hfood hN a d hd

end HordijkSteelThreshold
