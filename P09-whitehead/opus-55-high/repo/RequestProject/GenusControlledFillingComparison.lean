import RequestProject.GenusControlledCoverCap
import RequestProject.GenusCappedCoverAugmentation
import RequestProject.DavisFillingIndependence
import RequestProject.Tac
noncomputable section


/-! Comparison of the controlled and chosen cap fillings modulo actual three-boundaries. -/
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem rootedBaseCapFilling_hurewicz_eq x :
    hurewicz _ ((markedSpineToFullCube q).onV (markedSpineTree q).root)
      (rootedBaseCapFilling q x) =
    hurewicz _ (fullCubeMarkBase q) (fullCubeBaseCapChain q x) := by
  have haux (a : QCube (cmpRel _))
      (ha : endV (UV.base (orderCx (QCube (cmpRel _))) a) =
        fullCubeMarkBase q) :
      hurewicz _ a (fullCubeCoverCapChain q x _ ha) =
        hurewicz _ _ (fullCubeBaseCapChain q x) := by
    have he : a = fullCubeMarkBase q := ha
    subst a
    rfl
  unfold rootedBaseCapFilling SpanningTree.mappedTreeReference
  simp [← markedSpineTree_root q, SpanningTree.treePath_root, mapPath,
    List.map_nil, extendList_nil]
  simp_all

theorem chosenCap_controlled_difference_boundary3 x :
    ∃ y,
      ordBoundary3 y = hurewicz _ (fullCubeMarkBase q) (fullCubeBaseCapChain q x) -
        hurewicz _ (fullCubeMarkBase q) (controlledCoverCap q x) := by
  apply projected_fillings_difference_boundary3
  simp [fullCubeBaseCapChain, fullCubeCoverCapChain_boundary, controlledCoverCap_boundary]

theorem rootedCap_controlled_difference_boundary3 x :
    ∃ y,
      ordBoundary3 y = rootedAugmentedFace q (.inr x) -
        hurewicz _ (fullCubeMarkBase q) (controlledCoverCap q x) := by
  change ∃ y, ordBoundary3 y =
    hurewicz _ _
      (rootedBaseCapFilling q x) - _
  rwd [rootedBaseCapFilling_hurewicz_eq]
  exact chosenCap_controlled_difference_boundary3 q x

def controlledAugmentedFace : (cappedSpineCx q).F →
    (orderCx (QCube (cmpRel (GenusVertex q)))).F →₀ ℤ
  | .inl f => Finsupp.single ((markedSpineToFullCube q).onF f) 1
  | .inr x => hurewicz _ (fullCubeMarkBase q) (controlledCoverCap q x)

def controlledAugmentedChain2 :
    ((cappedSpineCx q).F →₀ ℤ) →ₗ[ℤ]
      ((orderCx (QCube (cmpRel (GenusVertex q)))).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (controlledAugmentedFace q)

/-- Replacing all chosen cap fillings by controlled fillings changes the comparison
only by an ordinary three-boundary. -/
theorem augmentedComparison_difference_boundary3 c :
    ∃ y,
      ordBoundary3 y = rootedAugmentedChain2 q c - controlledAugmentedChain2 q c := by
  induction c using Finsupp.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add c d hc hd =>
      cases' hc with y hy
      cases' hd with z hz
      refine ⟨y + z, ?_⟩
      rwd [map_add, hy, hz, map_add, map_add]
      abel
  | single f n =>
      obtain f | x := f
      · refine ⟨0, ?_⟩
        simp [rootedAugmentedChain2, controlledAugmentedChain2,
          rootedAugmentedFace, controlledAugmentedFace]
      · cases' rootedCap_controlled_difference_boundary3 q x with y hy
        refine ⟨n • y, ?_⟩
        rwd [map_smul, hy, rootedAugmentedChain2, controlledAugmentedChain2,
          Finsupp.linearCombination_single, Finsupp.linearCombination_single, smul_sub]
        rfl

/-- The controlled comparison of every actual capped-cover cycle is a three-boundary. -/
theorem controlledAugmentedCycle_boundary3 c
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ y,
      ordBoundary3 y = controlledAugmentedChain2 q (Finsupp.mapDomain Prod.snd c) := by
  cases' rootedAugmentedCycle_boundary3 q c hc with y hy
  obtain ⟨z, hz⟩ := augmentedComparison_difference_boundary3 q
    (Finsupp.mapDomain Prod.snd c)
  refine ⟨y - z, ?_⟩
  simp_all
