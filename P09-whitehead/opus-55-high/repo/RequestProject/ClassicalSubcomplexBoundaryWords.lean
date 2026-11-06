import RequestProject.HomeomorphContinuousMap
import RequestProject.ClassicalSubcomplexGraphNaturality
import RequestProject.BoundaryWordNaturality


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
      BoundaryFamily (RelCWComplex.cell (C : Set X) 2) (Fin 2 → ℝ)) :=
    ⟨fun x => ⟨j, x⟩, continuous_sigmaMk
      (σ := fun _ : RelCWComplex.cell (C : Set X) 2 => UnitBoundary (Fin 2 → ℝ)) (i := j)⟩
  exact (skeletonAsDiskAttachment _ 1).toContinuousMap.comp
    ((skeletonAttachingMap _ 2).comp a)

theorem subcomplexCellBoundary_natural h
    j :
    (subcomplexGraphDiskMap h).comp (subcomplexCellBoundary C j) =
      subcomplexCellBoundary D (subcomplexCellInclusion h 2 j) := by
  ext a
  apply (skeletonAttachmentHomeomorph _ 1).injective
  change skeletonAttachmentHomeomorph _ 1
    (subcomplexGraphDiskMap h (subcomplexCellBoundary C j a)) =
    skeletonAttachmentHomeomorph _ 1
      (subcomplexCellBoundary D (subcomplexCellInclusion h 2 j) a)
  rw [subcomplexGraphDiskMap_skeleton]
  change subcomplexSkeletonInclusion h 2
      ((skeletonAttachmentHomeomorph _ 1)
        ((skeletonAttachmentHomeomorph _ 1).symm _)) =
    (skeletonAttachmentHomeomorph _ 1)
      ((skeletonAttachmentHomeomorph _ 1).symm _)
  aesop

theorem subcomplexCellBoundary_word_exists
    (C : CWComplex.Subcomplex (Set.univ : Set X))
    j :
    ∃ W : BoundaryWords (skeletonAttachingMap (C : Set X) 1),
      (subcomplexCellBoundary C j).Homotopic W.boundaryMap := by
  letI := subcomplexZeroSkeleton_discrete C
  exact boundaryMap_homotopic_boundaryWords _
    (by fun_prop) _

theorem subcomplexBoundaryWord_map (h : (C : Set X) ⊆ D)
    (W : BoundaryWords (skeletonAttachingMap (C : Set X) 1)) :
    (subcomplexGraphDiskMap h).comp W.boundaryMap =
      (W.map (subcomplexGraphInclusion h)).boundaryMap :=
  W.boundaryMap_map (subcomplexGraphInclusion h) _
    (subcomplexGraphDiskMap_old h) (subcomplexGraphDiskMap_edge h)
