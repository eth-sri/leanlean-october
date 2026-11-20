module

public import RequestProject.GenusControlledCoverCap
public import RequestProject.GenusCappedCoverAugmentation
public import RequestProject.DavisFillingIndependence

@[expose] public section

/-! Comparison of the controlled and chosen cap fillings modulo actual three-boundaries. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem rootedBaseCapFilling_hurewicz_eq (x : Fin q × Bool) :
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
  simp_all [← markedSpineTree_root q, SpanningTree.treePath_root, mapPath, extendList_nil]

theorem chosenCap_controlled_difference_boundary3 (x : Fin q × Bool) :
    ∃ y : OrdTet (QCube (cmpRel (GenusVertex q))) →₀ ℤ,
      ordBoundary3 y = hurewicz _ (fullCubeMarkBase q) (fullCubeBaseCapChain q x) -
        hurewicz _ (fullCubeMarkBase q) (controlledCoverCap q x) := by
  apply projected_fillings_difference_boundary3
  erw [fullCubeBaseCapChain, fullCubeCoverCapChain_boundary, controlledCoverCap_boundary]

theorem rootedCap_controlled_difference_boundary3 (x : Fin q × Bool) :
    ∃ y : OrdTet (QCube (cmpRel (GenusVertex q))) →₀ ℤ,
      ordBoundary3 y = rootedAugmentedFace q (.inr x) -
        hurewicz _ (fullCubeMarkBase q) (controlledCoverCap q x) := by
  change ∃ y, ordBoundary3 y =
    hurewicz _ ((markedSpineToFullCube q).onV (markedSpineTree q).root)
      (rootedBaseCapFilling q x) - _
  erw [rootedBaseCapFilling_hurewicz_eq]
  exact chosenCap_controlled_difference_boundary3 q x

noncomputable def controlledAugmentedFace : (cappedSpineCx q).F →
    (orderCx (QCube (cmpRel (GenusVertex q)))).F →₀ ℤ
  | .inl f => Finsupp.single ((markedSpineToFullCube q).onF f) 1
  | .inr x => hurewicz _ (fullCubeMarkBase q) (controlledCoverCap q x)

noncomputable def controlledAugmentedChain2 :
    ((cappedSpineCx q).F →₀ ℤ) →ₗ[ℤ]
      ((orderCx (QCube (cmpRel (GenusVertex q)))).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (controlledAugmentedFace q)

/-- Replacing all chosen cap fillings by controlled fillings changes the comparison
only by an ordinary three-boundary. -/
theorem augmentedComparison_difference_boundary3 (c : (cappedSpineCx q).F →₀ ℤ) :
    ∃ y : OrdTet (QCube (cmpRel (GenusVertex q))) →₀ ℤ,
      ordBoundary3 y = rootedAugmentedChain2 q c - controlledAugmentedChain2 q c := by
  change _ ∈ LinearMap.range ordBoundary3
  apply Finsupp.map_mem_of_basis _ (rootedAugmentedChain2 q - controlledAugmentedChain2 q) _ c
  intro f
  obtain f | x := f
  · exact ⟨0, by simp [rootedAugmentedChain2, controlledAugmentedChain2,
      rootedAugmentedFace, controlledAugmentedFace]⟩
  · obtain ⟨y, hy⟩ := rootedCap_controlled_difference_boundary3 q x
    refine ⟨y, ?_⟩
    erw [LinearMap.sub_apply, rootedAugmentedChain2, controlledAugmentedChain2,
      Finsupp.linearCombination_single, Finsupp.linearCombination_single, one_smul, one_smul]
    exact hy

/-- The controlled comparison of every actual capped-cover cycle is a three-boundary. -/
theorem controlledAugmentedCycle_boundary3 (c : (cappedTreeCover q).F →₀ ℤ)
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ y : OrdTet (QCube (cmpRel (GenusVertex q))) →₀ ℤ,
      ordBoundary3 y = controlledAugmentedChain2 q (Finsupp.mapDomain Prod.snd c) := by
  obtain ⟨y, hy⟩ := rootedAugmentedCycle_boundary3 q c hc
  obtain ⟨z, hz⟩ := augmentedComparison_difference_boundary3 q
    (Finsupp.mapDomain Prod.snd c)
  refine ⟨y - z, ?_⟩
  erw [map_sub, hy, hz]
  abel

end FiniteChains.Davis.Genus
