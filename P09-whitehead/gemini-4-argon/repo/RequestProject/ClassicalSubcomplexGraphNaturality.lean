module

public import RequestProject.ClassicalCWGraphCoordinates
public import RequestProject.ComponentComplex

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment
open Set Topology
open scoped Classical unitInterval

variable {X : Type} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]
  {C D E : CWComplex.Subcomplex (Set.univ : Set X)}

def subcomplexCellInclusion (h : (C : Set X) ⊆ D) (n : ℕ) :
    RelCWComplex.cell (C : Set X) n ↪ RelCWComplex.cell (D : Set X) n :=
  ⟨fun j => ⟨j.val, by
      have hx := CWComplex.map_zero_mem_openCell (C := (Set.univ : Set X)) n j.val
      have hxD := h (C.openCell_subset_of_mem j.property hx)
      by_contra hn
      exact Set.disjoint_left.mp (D.disjoint_openCell_subcomplex_of_not_mem hn) hx hxD⟩,
    fun _ _ he => Subtype.ext (congrArg (fun z : RelCWComplex.cell (D : Set X) n => z.val) he)⟩

theorem subcomplex_skeleton_mono (h : (C : Set X) ⊆ D) (n : ℕ) :
    (CWComplex.skeletonLT (C : Set X) (n : ℕ∞) : Set X) ⊆
      CWComplex.skeletonLT (D : Set X) (n : ℕ∞) := fun x hx => by
  rw [← CWComplex.iUnion_openCell_eq_skeletonLT] at hx ⊢
  obtain ⟨m, hm, j, hxj⟩ := by simpa only [Set.mem_iUnion] using hx
  exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hm,
    Set.mem_iUnion.mpr ⟨subcomplexCellInclusion h m j, hxj⟩⟩⟩

def subcomplexSkeletonInclusion (h : (C : Set X) ⊆ D) (n : ℕ) :
    C(SkeletonCarrier (C : Set X) n, SkeletonCarrier (D : Set X) n) :=
  ⟨fun x => ⟨x.val, subcomplex_skeleton_mono h n x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

def subcomplexGraph (C : CWComplex.Subcomplex (Set.univ : Set X)) : Comb.Complex2 :=
  graphCx (skeletonAttachingMap (C : Set X) 1)

def subcomplexGraphInclusion (h : (C : Set X) ⊆ D) :
    Comb.Hom (subcomplexGraph C) (subcomplexGraph D) where
  onV := subcomplexSkeletonInclusion h 1
  onE := subcomplexCellInclusion h 1
  onF := Empty.elim
  src_onE _ := Subtype.ext rfl
  tgt_onE _ := Subtype.ext rfl
  base_onF f := Empty.elim f
  att_onF f := Empty.elim f

theorem subcomplexGraphInclusion_injective_V (h : (C : Set X) ⊆ D) :
    Function.Injective (subcomplexGraphInclusion h).onV :=
  fun _ _ he => Subtype.ext (congrArg (fun z : SkeletonCarrier (D : Set X) 1 => z.val) he)

theorem subcomplexGraphInclusion_injective_E (h : (C : Set X) ⊆ D) :
    Function.Injective (subcomplexGraphInclusion h).onE :=
  (subcomplexCellInclusion h 1).injective

theorem subcomplexGraphInclusion_comp (h : (C : Set X) ⊆ D)
    (k : (D : Set X) ⊆ E) :
    (subcomplexGraphInclusion k).comp (subcomplexGraphInclusion h) =
      subcomplexGraphInclusion (h.trans k) :=
  Comb.Hom.ext' rfl rfl (funext fun f => Empty.elim f)

theorem subcomplexZeroSkeleton_discrete (C : CWComplex.Subcomplex (Set.univ : Set X)) :
    DiscreteTopology (SkeletonCarrier (C : Set X) 1) :=
  ((zeroSkeleton_cellSeparated (X := X)).mono fun x hx => by
    rw [← CWComplex.iUnion_openCell_eq_skeletonLT] at hx ⊢
    obtain ⟨n, hn, j, hj⟩ := by simpa only [Set.mem_iUnion] using hx
    exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨hn,
      Set.mem_iUnion.mpr ⟨j.val, hj⟩⟩⟩).isDiscrete.to_subtype

def subcomplexDiskMap (h : (C : Set X) ⊆ D) (n : ℕ) :
    C(DiskAttachment (skeletonAttachingMap (C : Set X) n),
      DiskAttachment (skeletonAttachingMap (D : Set X) n)) :=
  (⟨_, (skeletonAsDiskAttachment (D : Set X) n).continuous⟩ :
      C(SkeletonCarrier (D : Set X) (n + 1), _)).comp
    ((subcomplexSkeletonInclusion h (n + 1)).comp
      ⟨_, (skeletonAttachmentHomeomorph (C : Set X) n).continuous⟩)

theorem subcomplexDiskMap_skeleton (h : (C : Set X) ⊆ D) (n : ℕ)
    (z : DiskAttachment (skeletonAttachingMap (C : Set X) n)) :
    skeletonAttachmentHomeomorph (D : Set X) n (subcomplexDiskMap h n z) =
      subcomplexSkeletonInclusion h (n + 1) (skeletonAttachmentHomeomorph (C : Set X) n z) :=
  (skeletonAttachmentHomeomorph (D : Set X) n).apply_symm_apply _

theorem subcomplexDiskMap_old (h : (C : Set X) ⊆ D) (n : ℕ)
    (x : SkeletonCarrier (C : Set X) n) :
    subcomplexDiskMap h n (old (skeletonAttachingMap (C : Set X) n) _ x) =
      old (skeletonAttachingMap (D : Set X) n) _ (subcomplexSkeletonInclusion h n x) :=
  (skeletonAttachmentHomeomorph (D : Set X) n).injective <| by
    rw [subcomplexDiskMap_skeleton]; exact Subtype.ext rfl

theorem subcomplexDiskMap_cell (h : (C : Set X) ⊆ D) (n : ℕ)
    (j : RelCWComplex.cell (C : Set X) n) (x : ClosedUnitBall (Fin n → ℝ)) :
    subcomplexDiskMap h n (cell (skeletonAttachingMap (C : Set X) n) _ ⟨j, x⟩) =
      cell (skeletonAttachingMap (D : Set X) n) _ ⟨subcomplexCellInclusion h n j, x⟩ :=
  (skeletonAttachmentHomeomorph (D : Set X) n).injective <| by
    rw [subcomplexDiskMap_skeleton]
    apply Subtype.ext
    change (skeletonAttachmentHomeomorph (C : Set X) n (cell _ _ ⟨j, x⟩)).val = _
    rw [skeletonAttachmentHomeomorph_cell, skeletonAttachmentHomeomorph_cell]; rfl

def subcomplexGraphDiskMap (h : (C : Set X) ⊆ D) :
    C(DiskAttachment (skeletonAttachingMap (C : Set X) 1),
      DiskAttachment (skeletonAttachingMap (D : Set X) 1)) := subcomplexDiskMap h 1

theorem subcomplexGraphDiskMap_skeleton (h : (C : Set X) ⊆ D)
    (z : DiskAttachment (skeletonAttachingMap (C : Set X) 1)) :
    skeletonAttachmentHomeomorph (D : Set X) 1 (subcomplexGraphDiskMap h z) =
      subcomplexSkeletonInclusion h 2 (skeletonAttachmentHomeomorph (C : Set X) 1 z) :=
  (skeletonAttachmentHomeomorph (D : Set X) 1).apply_symm_apply _

theorem subcomplexGraphDiskMap_old (h : (C : Set X) ⊆ D)
    (v : (subcomplexGraph C).V) :
    subcomplexGraphDiskMap h (old (skeletonAttachingMap (C : Set X) 1) _ v) =
      old (skeletonAttachingMap (D : Set X) 1) _ ((subcomplexGraphInclusion h).onV v) :=
  subcomplexDiskMap_old h 1 v

theorem subcomplexGraphDiskMap_edge (h : (C : Set X) ⊆ D)
    (j : (subcomplexGraph C).E) (t : I) :
    subcomplexGraphDiskMap h (graphEdgePath (skeletonAttachingMap (C : Set X) 1) j t) =
      graphEdgePath (skeletonAttachingMap (D : Set X) 1)
        ((subcomplexGraphInclusion h).onE j) t :=
  subcomplexDiskMap_cell h 1 j (graphDiskHomeomorph t)

theorem subcomplexGraphDiskMap_comp (h : (C : Set X) ⊆ D)
    (k : (D : Set X) ⊆ E) :
    (subcomplexGraphDiskMap k).comp (subcomplexGraphDiskMap h) =
      subcomplexGraphDiskMap (h.trans k) := by
  ext z
  apply (skeletonAttachmentHomeomorph (E : Set X) 1).injective
  change skeletonAttachmentHomeomorph (E : Set X) 1
    (subcomplexGraphDiskMap k (subcomplexGraphDiskMap h z)) =
    skeletonAttachmentHomeomorph (E : Set X) 1 (subcomplexGraphDiskMap (h.trans k) z)
  rw [subcomplexGraphDiskMap_skeleton, subcomplexGraphDiskMap_skeleton,
    subcomplexGraphDiskMap_skeleton]
  rfl

end FiniteChains.ClassicalCW
