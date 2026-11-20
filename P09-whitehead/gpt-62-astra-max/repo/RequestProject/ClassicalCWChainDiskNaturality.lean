module

public import RequestProject.ClassicalCWChainDiskModels

@[expose] public section

/-! The coherent word-disk models form actual commuting squares with
the original subcomplex inclusions. Thus original topological pi2
vanishing transfers to the constructed model inclusions. Unverified. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment
open Set Topology
open scoped Classical
variable (K : Whitehead.TwoComplex)

theorem subcomplexAsDiskAttachment_natural
    {C D : CWComplex.Subcomplex Set.univ} (h : (C : Set K) ⊆ D)
    (x : (C : Set K)) :
    subcomplexAsDiskAttachment K D (Set.inclusion h x) =
      subcomplexDiskMap h 2 (subcomplexAsDiskAttachment K C x) := by
  apply (skeletonAttachmentHomeomorph (D : Set K) 2).injective
  rw [subcomplexDiskMap_skeleton]
  change (skeletonAttachmentHomeomorph (D : Set K) 2)
      ((skeletonAttachmentHomeomorph (D : Set K) 2).symm _) =
    subcomplexSkeletonInclusion h 3
      ((skeletonAttachmentHomeomorph (C : Set K) 2)
        ((skeletonAttachmentHomeomorph (C : Set K) 2).symm _))
  aesop

namespace ChainWords
variable {n : ℕ} (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C)
  [Choices C]

variable {i k : Fin (n + 1)} (hik : i ≤ k)

variable (j : RelCWComplex.cell (C i : Set K) 2) (a : UnitBoundary (Fin 2 → ℝ))

omit [Choices C] in
theorem rawAttaching_natural :
    subcomplexGraphDiskMap (hC hik) (rawAttaching C i ⟨j, a⟩) =
      rawAttaching C k ⟨subcomplexCellInclusion (hC hik) 2 j, a⟩ :=
  congrArg (fun f => f a) (subcomplexCellBoundary_natural (hC hik) j)

theorem wordAttaching_natural :
    subcomplexGraphDiskMap (hC hik) (wordAttaching C hC i ⟨j, a⟩) =
      wordAttaching C hC k ⟨subcomplexCellInclusion (hC hik) 2 j, a⟩ := by
  change subcomplexGraphDiskMap _ ((word C hC i j).boundaryMap a) =
    (word C hC k _).boundaryMap a
  rw [word_natural C hC hik]
  exact congrArg (fun f => f a) (subcomplexBoundaryWord_map (hC hik) _)

def rawDiskInclusion :=
  diskFamilyMap _ _ _
    _ (rawAttaching_natural K C hC hik)

def wordDiskInclusion :=
  diskFamilyMap _ _
    _ _
    (wordAttaching_natural K C hC hik)

theorem wordDiskChange_natural :
    (wordDiskInclusion K C hC hik).comp (wordDiskChange C hC i).toFun =
      (wordDiskChange C hC k).toFun.comp (rawDiskInclusion K C hC hik) :=
  naturalDiskAttachingEquiv_natural _ _ _
    _ _ _ _
    _ _
    _
    (fun t j a => (attachingHomotopy_natural C hC hik j t a).symm)

def rawBaseChange (i : Fin _) :=
  diskAttachmentBaseChangeHomotopyEquiv (skeletonAttachingMap (C i : Set K) 2)
    (skeletonAsDiskAttachment (C i : Set K) 1).toHomotopyEquiv

variable {i k : Fin (n + 1)} (hik : i ≤ k)

omit [Choices C] in
theorem rawBaseChange_natural :
    (rawDiskInclusion K C hC hik).comp (rawBaseChange K C i).toFun =
      (rawBaseChange K C k).toFun.comp (subcomplexDiskMap (hC hik) 2) := by
  apply hom_ext (skeletonAttachingMap (C i : Set K) 2)
    (boundaryFamilyInclusion _ _)
  · intro x
    change rawDiskInclusion K C hC hik
      (diskAttachmentBaseChangeHomotopyEquiv (skeletonAttachingMap (C i : Set K) 2)
        (skeletonAsDiskAttachment (C i : Set K) 1).toHomotopyEquiv
        (old (skeletonAttachingMap (C i : Set K) 2)
          (boundaryFamilyInclusion (RelCWComplex.cell (C i : Set K) 2) (Fin 2 → ℝ)) x)) = _
    change diskFamilyMap _ _ _ _ _ (old _ _ _) =
      diskAttachmentBaseChangeHomotopyEquiv _ _ (subcomplexDiskMap _ 2 _)
    rw [diskFamilyMap_old, subcomplexDiskMap_old, diskAttachmentBaseChangeHomotopyEquiv_old]
    congr 1
    change (skeletonAttachmentHomeomorph (C k : Set K) 1).symm
      (subcomplexSkeletonInclusion (hC hik) 2
        ((skeletonAttachmentHomeomorph (C i : Set K) 1)
          ((skeletonAttachmentHomeomorph (C i : Set K) 1).symm x))) = _
    aesop
  · rintro ⟨j, x⟩
    change rawDiskInclusion K C hC hik (diskAttachmentBaseChangeHomotopyEquiv _ _ (cell _ _ ⟨j, x⟩)) = _
    rw [diskAttachmentBaseChangeHomotopyEquiv_cell]
    change diskFamilyMap _ _ _ _ _ (cell _ _ _) =
      diskAttachmentBaseChangeHomotopyEquiv _ _ (subcomplexDiskMap _ 2 _)
    rw [diskFamilyMap_cell, subcomplexDiskMap_cell, diskAttachmentBaseChangeHomotopyEquiv_cell]
    rfl

omit [Choices C] in
theorem rawDiskEquiv_natural (x : (C i : Set K)) :
    rawDiskInclusion K C hC hik (rawDiskEquiv K C i x) =
      rawDiskEquiv K C k (Set.inclusion (hC hik) x) := by
  change rawDiskInclusion K C hC hik
      _ =
    rawBaseChange K C k (subcomplexAsDiskAttachment K (C k) (Set.inclusion (hC hik) x))
  rw [subcomplexAsDiskAttachment_natural K _ x]
  exact congrArg (fun f => f (subcomplexAsDiskAttachment K (C i) x))
    (rawBaseChange_natural K C hC hik)

theorem wordDiskEquiv_natural :
    (wordDiskInclusion K C hC hik).comp (wordDiskEquiv K C hC i).toFun =
      (wordDiskEquiv K C hC k).toFun.comp
        ⟨Set.inclusion _, continuous_inclusion (hC hik)⟩ := by
  ext x
  change wordDiskInclusion K C hC hik (wordDiskChange C hC i (rawDiskEquiv K C i x)) = _
  have h := congrArg (fun f => f (rawDiskEquiv K C i x)) (wordDiskChange_natural K C hC hik)
  change wordDiskInclusion K C hC hik _ =
    wordDiskChange C hC k _ at h
  rw [h, rawDiskEquiv_natural]
  rfl

theorem wordDiskInclusion_killsPi2_iff :
    Whitehead.KillsPi2 (wordDiskInclusion K C hC hik) ↔
      Whitehead.KillsPi2 (⟨Set.inclusion _, continuous_inclusion (hC hik)⟩) := by
  apply Whitehead.killsPi2_homotopyEquiv_square_iff
    (wordDiskEquiv K C hC i) (wordDiskEquiv K C hC k)
  rw [wordDiskEquiv_natural]

end ChainWords
end FiniteChains.ClassicalCW
