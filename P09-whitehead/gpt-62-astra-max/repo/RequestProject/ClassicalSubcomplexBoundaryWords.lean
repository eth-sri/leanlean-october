module


public import RequestProject.ClassicalSubcomplexGraphNaturality
public import RequestProject.BoundaryWordNaturality

@[expose] public section

/-! Every original two-cell has a boundary word in the exact graph of
its subcomplex. These data can be pushed along original inclusions,
including their actual attaching homotopy. Unverified source. -/

noncomputable section
namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment
open Set Topology
open scoped Classical
variable {X : Type} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]
  {C D : CWComplex.Subcomplex (Set.univ : Set X)}

def subcomplexCellBoundary (C : CWComplex.Subcomplex (Set.univ : Set X))
    (j : RelCWComplex.cell (C : Set X) 2) :
    C(UnitBoundary (Fin 2 → ℝ), DiskAttachment (skeletonAttachingMap (C : Set X) 1)) := by
  let a : C(UnitBoundary (Fin 2 → ℝ),
      BoundaryFamily _ (Fin 2 → ℝ)) :=
    ⟨fun x => ⟨j, x⟩, continuous_sigmaMk
      (σ := fun _ : RelCWComplex.cell (C : Set X) 2 => UnitBoundary (Fin 2 → ℝ))⟩
  exact (skeletonAsDiskAttachment (C : Set X) 1).toContinuousMap.comp
    ((skeletonAttachingMap (C : Set X) 2).comp a)

theorem subcomplexCellBoundary_natural (h : (C : Set X) ⊆ D)
    (j : RelCWComplex.cell (C : Set X) 2) :
    (subcomplexGraphDiskMap h).comp (subcomplexCellBoundary C j) =
      subcomplexCellBoundary D (subcomplexCellInclusion h 2 j) := by
  ext a
  apply (skeletonAttachmentHomeomorph (D : Set X) 1).injective
  change skeletonAttachmentHomeomorph _ 1
    (subcomplexGraphDiskMap h _) =
    skeletonAttachmentHomeomorph _ 1
      (subcomplexCellBoundary D _ a)
  rw [subcomplexGraphDiskMap_skeleton]
  change subcomplexSkeletonInclusion h 2
      ((skeletonAttachmentHomeomorph (C : Set X) 1)
        ((skeletonAttachmentHomeomorph (C : Set X) 1).symm _)) =
    (skeletonAttachmentHomeomorph (D : Set X) 1)
      ((skeletonAttachmentHomeomorph (D : Set X) 1).symm _)
  aesop

theorem subcomplexCellBoundary_word_exists
    (C : CWComplex.Subcomplex (Set.univ : Set X))
    (j : RelCWComplex.cell (C : Set X) 2) :
    ∃ W : BoundaryWords _,
      (subcomplexCellBoundary C j).Homotopic W.boundaryMap := by
  letI := subcomplexZeroSkeleton_discrete C
  exact boundaryMap_homotopic_boundaryWords _
    (skeletonAttachingMap (C : Set X) 1).continuous _

theorem subcomplexBoundaryWord_map (h : (C : Set X) ⊆ D)
    (W : BoundaryWords _) :
    (subcomplexGraphDiskMap h).comp W.boundaryMap =
      (W.map (subcomplexGraphInclusion h)).boundaryMap :=
  W.boundaryMap_map _ (subcomplexGraphDiskMap h)
    (subcomplexGraphDiskMap_old h) (subcomplexGraphDiskMap_edge h)

end FiniteChains.ClassicalCW
