import Mathlib.Tactic

import RequestProject.GenusControlledCoverCap
import RequestProject.GenusCappedCoverAugmentation
import RequestProject.DavisFillingIndependence

/-! Comparison of the controlled and chosen cap fillings modulo actual three-boundaries. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

  (x : Fin q × Bool)
theorem rootedBaseCapFilling_hurewicz_eq  :
    hurewicz _ ((markedSpineToFullCube q).onV (markedSpineTree q).root)
      (rootedBaseCapFilling q x) =
    hurewicz _ (fullCubeMarkBase q) (fullCubeBaseCapChain q x) := by
  have haux (a : QCube (cmpRel (GenusVertex q)))
      (ha : endV (UV.base (orderCx (QCube (cmpRel (GenusVertex q)))) a) =
        fullCubeMarkBase q) :
      hurewicz _ a (fullCubeCoverCapChain q x (UV.base (orderCx (QCube (cmpRel (GenusVertex q)))) a) ha) =
        hurewicz _ (fullCubeMarkBase q) (fullCubeBaseCapChain q x) := by
    have he : a = fullCubeMarkBase q := ha
    subst a
    rfl
  unfold rootedBaseCapFilling SpanningTree.mappedTreeReference
  simp [← markedSpineTree_root q]
  exact haux _ _

theorem chosenCap_controlled_difference_boundary3  :
    ∃ y : OrdTet (QCube (cmpRel (GenusVertex q))) →₀ ℤ,
      ordBoundary3 y = hurewicz _ (fullCubeMarkBase q) (fullCubeBaseCapChain q x) -
        hurewicz _ (fullCubeMarkBase q) (controlledCoverCap q x) := by
  apply projected_fillings_difference_boundary3
  rw  [fullCubeBaseCapChain, fullCubeCoverCapChain_boundary, controlledCoverCap_boundary]

theorem rootedCap_controlled_difference_boundary3  :
    ∃ y : OrdTet (QCube (cmpRel (GenusVertex q))) →₀ ℤ,
      ordBoundary3 y = rootedAugmentedFace q (.inr x) -
        hurewicz _ (fullCubeMarkBase q) (controlledCoverCap q x) := by
  dsimp!
  rw (config := { transparency := .default }) [rootedBaseCapFilling_hurewicz_eq]
  exact chosenCap_controlled_difference_boundary3 q x

noncomputable def controlledAugmentedFace : (cappedSpineCx q).F →
    (orderCx (QCube (cmpRel (GenusVertex q)))).F →₀ ℤ
  | .inl f => Finsupp.single ((markedSpineToFullCube q).onF f) 1
  | .inr x => hurewicz _ (fullCubeMarkBase q) (controlledCoverCap q x)

noncomputable def controlledAugmentedChain2  :=
  Finsupp.linearCombination ℤ (controlledAugmentedFace q)

/-- Replacing all chosen cap fillings by controlled fillings changes the comparison
only by an ordinary three-boundary. -/
theorem augmentedComparison_difference_boundary3 (c : (cappedSpineCx q).F →₀ ℤ) :
    ∃ y : OrdTet (QCube (cmpRel (GenusVertex q))) →₀ ℤ,
      ordBoundary3 y = rootedAugmentedChain2 q c - controlledAugmentedChain2 q c := by
  induction c using Finsupp.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add c d hc hd =>
      obtain ⟨y, hy⟩ := hc
      obtain ⟨z, hz⟩ := hd
      refine ⟨y + z, ?_⟩
      rw  [map_add, hy, hz, map_add, map_add]
      abel
  | single f n =>
      obtain f | x := f
      · refine ⟨0, ?_⟩
        simp [rootedAugmentedChain2, controlledAugmentedChain2,
          rootedAugmentedFace, controlledAugmentedFace]
      · obtain ⟨y, hy⟩ := rootedCap_controlled_difference_boundary3 q x
        refine ⟨n • y, ?_⟩
        rw  [map_smul, hy, rootedAugmentedChain2, controlledAugmentedChain2,
          Finsupp.linearCombination_single, Finsupp.linearCombination_single, smul_sub]
        rfl

/-- The controlled comparison of every actual capped-cover cycle is a three-boundary. -/
theorem controlledAugmentedCycle_boundary3 (c : (cappedTreeCover q).F →₀ ℤ)
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ y : OrdTet (QCube (cmpRel (GenusVertex q))) →₀ ℤ,
      ordBoundary3 y = controlledAugmentedChain2 q (Finsupp.mapDomain Prod.snd c) := by
  obtain ⟨y, hy⟩ := rootedAugmentedCycle_boundary3 q c hc
  obtain ⟨z, hz⟩ := augmentedComparison_difference_boundary3 q
    (Finsupp.mapDomain Prod.snd c)
  refine ⟨y - z, ?_⟩
  rw  [map_sub, hy, hz]
  abel

end FiniteChains.Davis.Genus
