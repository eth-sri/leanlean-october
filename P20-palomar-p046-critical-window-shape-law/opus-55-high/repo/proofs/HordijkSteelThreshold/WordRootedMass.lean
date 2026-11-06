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

variable {L N w : ℕ} (hL : 2*w ≤ L) (ω : Reaction N → Prop)

noncomputable def badMolecularWords  : Finset (ActualBinaryWord N) :=
  Finset.univ.filter $ fun s => moleculeContourBad hL s.val ω

noncomputable def rootedMolecularWords  : Finset (ActualBinaryWord N) :=
  Finset.univ.filter $ fun s => indexedEdgeReach (wordEffectiveEdges hL ω) Prod.fst wordEdgeParent
    (boundedFoodRoot L N) $ molecularWordVertex L N s.val


theorem molecularWordVertex_food {L N : ℕ} (s : List Bool) (hs : s.length ≤ L) :
    molecularWordVertex L N s = boundedFoodRoot L N := by
  simp [molecularWordVertex, not_lt.mpr hs]

end HordijkSteelThreshold
