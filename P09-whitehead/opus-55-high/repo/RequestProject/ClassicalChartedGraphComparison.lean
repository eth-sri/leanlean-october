import RequestProject.HomeomorphContinuousMap
import RequestProject.ClassicalCWRecharacterization
import RequestProject.ClassicalSubcomplexBoundaryWords
import RequestProject.Tac


/-! An embedding preserving characteristic maps identifies the literal
old graph, its intervals, and every original two-cell boundary with the
corresponding subcomplex data. Recharacterization supplies precisely this
hypothesis from the original InitialIdentification. Unverified source. -/

noncomputable section
open scoped Classical
open Set Topology
bwd

namespace Whitehead.CWCellEmbedding
open FiniteChains FiniteChains.ClassicalCW FiniteChains.ClassicalGraphModel
open FiniteChains.ClassicalSkeletonAttachment FiniteChains.RelativeAttachment
variable {K L : TwoComplex} (e : CWCellEmbedding K L)

theorem skeleton_image (n : ℕ) :
    e.map '' (CWComplex.skeletonLT (Set.univ : Set K) n) =
      (CWComplex.skeletonLT (e.imageSubcomplex : Set L) n) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← CWComplex.iUnion_openCell_eq_skeletonLT] at hx ⊢
    obtain ⟨m, hm, j, hj⟩ := by simpa only [Set.mem_iUnion] using hx
    apply Set.mem_iUnion.mpr
    refine ⟨m, Set.mem_iUnion.mpr ⟨hm, Set.mem_iUnion.mpr ⟨e.imageCellEquiv m j, ?_⟩⟩⟩
    change e.map x ∈ CWComplex.openCell (C := Set.univ) m (e.cellIndex m j)
    rw [← e.openCell_image]
    tauto
  · intro hy
    rw [← CWComplex.iUnion_openCell_eq_skeletonLT] at hy
    obtain ⟨m, hm, j, hj⟩ := by simpa only [Set.mem_iUnion] using hy
    cases' j.property with a ha
    change y ∈ CWComplex.openCell (C := Set.univ) m j.val at hj
    rw [← ha, ← e.openCell_image] at hj
    obtain ⟨x, hx, rfl⟩ := hj
    refine ⟨x, ?_, rfl⟩
    rw [← CWComplex.iUnion_openCell_eq_skeletonLT]
    aesop

theorem skeletonMap_mem n (x : SkeletonCarrier Set.univ n) :
    e.map x.val ∈ (CWComplex.skeletonLT (e.imageSubcomplex : Set L) n : Set L) :=
  (skeleton_image e n).subset (by aesop)

def skeletonMap n :
    C(SkeletonCarrier (Set.univ : Set K) n, SkeletonCarrier (e.imageSubcomplex : Set L) n) where
  toFun x := ⟨e.map x.val, skeletonMap_mem e n x⟩
  continuous_toFun := (e.map.continuous.comp continuous_subtype_val).subtype_mk _

theorem skeletonMap_isEmbedding n : IsEmbedding (skeletonMap e n) := by
  apply IsEmbedding.subtypeVal.of_comp_iff.mp
  exact e.closedEmbedding.isEmbedding.comp IsEmbedding.subtypeVal

theorem skeletonMap_surjective n : Function.Surjective (skeletonMap e n) := by
  intro y
  have hy : y.val ∈ (CWComplex.skeletonLT (e.imageSubcomplex : Set L) (n : ℕ∞) : Set L) := y.property
  rw [← skeleton_image] at hy
  aesop

def skeletonHomeomorph n :=
  (skeletonMap_isEmbedding e n).toHomeomorphOfSurjective (skeletonMap_surjective e n)

variable (hchart : ∀ n (j : RelCWComplex.cell (Set.univ : Set K) n) (x : Fin n → ℝ),
  RelCWComplex.map (C := (Set.univ : Set L)) n (e.cellIndex n j) x =
    e.map (RelCWComplex.map (C := (Set.univ : Set K)) n j x))

def graphHom : Comb.Hom (originalGraph K) (subcomplexGraph e.imageSubcomplex) where
  onV := skeletonMap e 1
  onE := e.imageCellEquiv 1
  onF := Empty.elim
  src_onE j := Subtype.ext (hchart 1 j _)
  tgt_onE j := Subtype.ext (hchart 1 j _)
  base_onF f := nomatch f
  att_onF f := nomatch f

theorem graphHom_injective_V : Function.Injective (graphHom e hchart).onV :=
  (skeletonMap_isEmbedding e 1).injective

theorem graphHom_injective_E : Function.Injective (graphHom e hchart).onE :=
  (e.imageCellEquiv 1).injective

def graphDiskHomeomorph : DiskAttachment (originalGraphAttaching K) ≃ₜ
    DiskAttachment (skeletonAttachingMap (e.imageSubcomplex : Set L) 1) :=
  ((skeletonAttachmentHomeomorph _ 1).trans (skeletonHomeomorph e 2)).trans
    (skeletonAsDiskAttachment _ 1)

theorem graphDiskHomeomorph_skeleton x :
    skeletonAttachmentHomeomorph (e.imageSubcomplex : Set L) 1 (graphDiskHomeomorph e x) =
      skeletonMap e 2 (skeletonAttachmentHomeomorph Set.univ 1 x) :=
  (skeletonAttachmentHomeomorph _ 1).apply_symm_apply _

theorem graphDiskHomeomorph_old (v : (originalGraph K).V) :
    graphDiskHomeomorph e (old (originalGraphAttaching K) _ v) =
      old (skeletonAttachingMap (e.imageSubcomplex : Set L) 1) _ ((graphHom e hchart).onV v) := by
  apply (skeletonAttachmentHomeomorph _ 1).injective
  rw [graphDiskHomeomorph_skeleton]
  rfl

theorem graphDiskHomeomorph_cell (j : (originalGraph K).E) x :
    graphDiskHomeomorph e (cell (originalGraphAttaching K) _ ⟨j, x⟩) =
      cell (skeletonAttachingMap (e.imageSubcomplex : Set L) 1) _ ⟨(graphHom e hchart).onE j, x⟩ := by
  apply (skeletonAttachmentHomeomorph _ 1).injective
  rw [graphDiskHomeomorph_skeleton]
  apply Subtype.ext
  change e.map ((skeletonAttachmentHomeomorph _ 1 (cell _ _ ⟨j, x⟩)).val) =
    (skeletonAttachmentHomeomorph (e.imageSubcomplex : Set L) 1 (cell _ _ ⟨e.imageCellEquiv 1 j, x⟩)).val
  rw [skeletonAttachmentHomeomorph_cell, skeletonAttachmentHomeomorph_cell]
  exact (hchart 1 j x.val).symm

theorem graphDiskHomeomorph_edge (j : (originalGraph K).E) t :
    graphDiskHomeomorph e (graphEdgePath (originalGraphAttaching K) j t) =
      graphEdgePath (skeletonAttachingMap (e.imageSubcomplex : Set L) 1)
        ((graphHom e hchart).onE j) t :=
  graphDiskHomeomorph_cell e hchart j _

end Whitehead.CWCellEmbedding

namespace FiniteChains.ClassicalCW
open ClassicalGraphModel ClassicalSkeletonAttachment RelativeAttachment

def originalGraphCellBoundary (K : Whitehead.TwoComplex)
    (j : RelCWComplex.cell (Set.univ : Set K) 2) :
    C(UnitBoundary (Fin 2 → ℝ), DiskAttachment (originalGraphAttaching K)) :=
  (skeletonAsDiskAttachment _ 1).toContinuousMap.comp
    ((skeletonAttachingMap _ 2).comp ⟨fun a => ⟨j, a⟩, continuous_sigmaMk (σ := fun _ : RelCWComplex.cell (Set.univ : Set K) 2 => UnitBoundary (Fin 2 → ℝ)) (i := j)⟩)

theorem originalGraphCellBoundary_word_exists K
    j :
    ∃ W : BoundaryWords (originalGraphAttaching K),
      (originalGraphCellBoundary K j).Homotopic W.boundaryMap := by
  letI := zeroSkeleton_discrete (X := K)
  exact boundaryMap_homotopic_boundaryWords _
    (originalGraphAttaching K).continuous _

def fixedGraphWord (K : Whitehead.TwoComplex) (j : RelCWComplex.cell (Set.univ : Set K) 2) :=
  Classical.choose (originalGraphCellBoundary_word_exists K j)

theorem fixedGraphWord_spec K
    j :
    (originalGraphCellBoundary K j).Homotopic (fixedGraphWord K j).boundaryMap :=
  Classical.choose_spec (originalGraphCellBoundary_word_exists K j)

end FiniteChains.ClassicalCW

namespace Whitehead.CWCellEmbedding
open FiniteChains FiniteChains.ClassicalCW FiniteChains.ClassicalGraphModel
open FiniteChains.ClassicalSkeletonAttachment FiniteChains.RelativeAttachment
variable {K L : TwoComplex} (e : CWCellEmbedding K L)
  (hchart : ∀ n (j : RelCWComplex.cell (Set.univ : Set K) n) (x : Fin n → ℝ),
    RelCWComplex.map (C := (Set.univ : Set L)) n (e.cellIndex n j) x =
      e.map (RelCWComplex.map (C := (Set.univ : Set K)) n j x))

include hchart in
theorem originalGraphCellBoundary_natural (j : RelCWComplex.cell (Set.univ : Set K) 2) :
    (graphDiskHomeomorph e).toContinuousMap.comp (originalGraphCellBoundary K j) =
      subcomplexCellBoundary e.imageSubcomplex (e.imageCellEquiv 2 j) := by
  ext a
  apply (skeletonAttachmentHomeomorph _ 1).injective
  change skeletonAttachmentHomeomorph _ 1
    (graphDiskHomeomorph e (originalGraphCellBoundary K j a)) = _
  rw [graphDiskHomeomorph_skeleton]
  change skeletonMap e 2
      (skeletonAttachmentHomeomorph (Set.univ : Set K) 1
        ((skeletonAttachmentHomeomorph _ 1).symm _)) =
    skeletonAttachmentHomeomorph (e.imageSubcomplex : Set L) 1
      ((skeletonAttachmentHomeomorph _ 1).symm _)
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  apply Subtype.ext
  exact (hchart 2 j a.val).symm

theorem fixedGraphWord_transport j :
    (subcomplexCellBoundary e.imageSubcomplex (e.imageCellEquiv 2 j)).Homotopic
      ((fixedGraphWord K j).map (graphHom e hchart)).boundaryMap := by
  have H := (ContinuousMap.Homotopic.refl (graphDiskHomeomorph e).toContinuousMap).comp
    (fixedGraphWord_spec K j)
  rw [originalGraphCellBoundary_natural e hchart] at H
  have he := BoundaryWords.boundaryMap_map _
    (graphDiskHomeomorph e).toContinuousMap (graphDiskHomeomorph_old e hchart)
    (graphDiskHomeomorph_edge e hchart) (fixedGraphWord K j)
  simp_all
