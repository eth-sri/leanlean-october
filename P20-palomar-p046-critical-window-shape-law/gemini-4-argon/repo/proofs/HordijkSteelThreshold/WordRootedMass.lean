module

public import proofs.HordijkSteelThreshold.WordRootedCoverage
public import proofs.HordijkSteelThreshold.ContourMassBound

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer unitInterval

abbrev ActualBinaryWord (N : ℕ) := ↥(actualBinaryWords N)

def actualBinaryRoot (N : ℕ) (hN : 0 < N) : ActualBinaryWord N :=
  ⟨[false], (mem_actualBinaryWords [false] N).mpr ⟨by simp,
    by simpa using (show 1 ≤ N by omega)⟩⟩

noncomputable def badMolecularWords {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) : Finset (ActualBinaryWord N) :=
  Finset.univ.filter (fun s => moleculeContourBad hL s.val ω)

noncomputable def rootedMolecularWords {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) : Finset (ActualBinaryWord N) :=
  Finset.univ.filter (fun s => indexedEdgeReach (wordEffectiveEdges hL ω) Prod.fst wordEdgeParent
    (boundedFoodRoot L N) (molecularWordVertex L N s.val))

theorem molecularWordVertex_food {L N : ℕ} (s : List Bool) (hs : s.length ≤ L) :
    molecularWordVertex L N s = boundedFoodRoot L N := by
  simp [molecularWordVertex, not_lt.mpr hs]

theorem measure_rootedMolecularWords_deficit {L N w k : ℕ} (hL : 2*w ≤ L)
    (hk : 5*k ≤ w) (hfood : 0 < L) (hN : 0 < N) (a : I) (d : ℕ) (hd : 0 < d) :
    staticReactionMeasure N a {ω | (rootedMolecularWords hL ω).card+d ≤
      (actualBinaryWords N).card} ≤
      contourBudget a k/(1-contourBudget a k) +
      ((actualBinaryWords N).card : ENNReal)*(contourBudget a k/(1-contourBudget a k))/d := by
  simpa only [Fintype.card_coe] using measure_pool_deficit_le (staticReactionMeasure N a)
    (badMolecularWords hL) (rootedMolecularWords hL) (actualBinaryRoot N hN)
    (fun ω hr s hs => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      have hp := outside_moleculeContourBad_connected hL ω (actualBinaryRoot N hN).val s.val
        (actualBinaryRoot N hN).property s.property
        (by simpa [badMolecularWords] using hr) (by simpa [badMolecularWords] using hs)
      rwa [molecularWordVertex_food _ (by simp [actualBinaryRoot]; omega)] at hp⟩)
    (contourBudget a k/(1-contourBudget a k))
    (fun s => by simpa [badMolecularWords] using measure_moleculeContourBad_le hL hk s.val a) d hd

end HordijkSteelThreshold
