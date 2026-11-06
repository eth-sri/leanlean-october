import Mathlib.Tactic

import RequestProject.GenusCappedCoverChainMap
import RequestProject.UniversalThreeAugmentation

/-! The exact deck-forgetting formula for the constructed capped-cover comparison. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb

variable (q : ℕ) [NeZero q]

noncomputable def rootedAugmentedFace : (cappedSpineCx q).F →
    (orderCx (QCube (cmpRel (GenusVertex q)))).F →₀ ℤ
  | .inl f => Finsupp.single ((markedSpineToFullCube q).onF f) 1
  | .inr x => hurewicz _ ((markedSpineToFullCube q).onV (markedSpineTree q).root)
      (rootedBaseCapFilling q x)

noncomputable def rootedAugmentedChain2  :=
  Finsupp.linearCombination ℤ (rootedAugmentedFace q)

variable (c : (cappedTreeCover q).F →₀ ℤ)
/-- The constructed full comparison commutes with forgetting the actual deck coordinate. -/
theorem rootedCoverChain2_hurewicz  :
    hurewicz _ ((markedSpineToFullCube q).onV (markedSpineTree q).root)
      (rootedCoverChain2 q c) = rootedAugmentedChain2 q (Finsupp.mapDomain Prod.snd c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      simp_all [Finsupp.mapDomain_add]
  | single gf n =>
      rw  [rootedCoverChain2, Finsupp.linearCombination_single, map_smul,
        Finsupp.mapDomain_single, rootedAugmentedChain2, Finsupp.linearCombination_single]
      congr 1
      obtain ⟨g, f | x⟩ := gf
      · solve_by_elim [Finsupp.mapDomain_single]
      · exact hurewicz_deck_faceChains _ _ _

/-- The augmented comparison of a genuine capped-cover cycle is an actual three-boundary. -/
theorem rootedAugmentedCycle_boundary3 
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ y : OrdTet (QCube (cmpRel (GenusVertex q))) →₀ ℤ,
      ordBoundary3 y = rootedAugmentedChain2 q (Finsupp.mapDomain Prod.snd c) := by
  obtain ⟨z, hz⟩ := rootedCoverCycle_fullCube_filling q c hc
  refine ⟨Finsupp.mapDomain (fun t => t.1.2) z, ?_⟩
  rw  [← hurewicz_uOrdBoundary3, hz, rootedCoverChain2_hurewicz]

end FiniteChains.Davis.Genus
