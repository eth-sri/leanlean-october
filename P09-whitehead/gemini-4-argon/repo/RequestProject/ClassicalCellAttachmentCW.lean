module

public import RequestProject.ClassicalCellAttachmentHausdorff

@[expose] public section

noncomputable section
open scoped Classical
open Set Topology Metric

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.RelativeAttachment

variable {X J : Type} [TopologicalSpace X] [Nonempty X]
  [CWComplex (Set.univ : Set X)]
variable (n : ℕ) (r : BoundaryFamily J (Fin n → ℝ) → X) (hr : Continuous r) (x₀ : X)

def FiniteLowerBoundary : Prop := ∀ j : J,
  ∃ I : ∀ m, Finset (RelCWComplex.cell (Set.univ : Set X) m),
    ∀ a : UnitBoundary (Fin n → ℝ),
      r ⟨j, a⟩ ∈ ⋃ (m < n) (k ∈ I m), RelCWComplex.closedCell m k

abbrev AttachmentCell (m : ℕ) :=
  RelCWComplex.cell (Set.univ : Set X) m ⊕ {_j : J // m = n}

def attachmentCharacteristic (m : ℕ) : AttachmentCell (X := X) (J := J) n m →
    PartialEquiv (Fin m → ℝ) (DiskAttachment r)
  | Sum.inl j => ClosedEmbeddingCW.imageCharacteristic
      (old r (boundaryFamilyInclusion J (Fin n → ℝ)))
      (old_isClosedEmbedding r _ hr (boundaryFamilyInclusion_isClosedEmbedding J (Fin n → ℝ))) m j
  | Sum.inr ⟨j, h⟩ => h ▸ diskCharacteristic r x₀ j

@[simp] theorem attachmentCharacteristic_new (j : J) :
    attachmentCharacteristic n r hr x₀ n (Sum.inr ⟨j, rfl⟩) =
      diskCharacteristic r x₀ j := rfl

theorem attachmentCharacteristic_old_image (m : ℕ)
    (j : RelCWComplex.cell (Set.univ : Set X) m) (S : Set (Fin m → ℝ)) :
    attachmentCharacteristic n r hr x₀ m (Sum.inl j) '' S =
      old r (boundaryFamilyInclusion J (Fin n → ℝ)) '' (RelCWComplex.map m j '' S) :=
  ClosedEmbeddingCW.imageCharacteristic_image _ _ m j S

variable [T2Space X]

def attachmentCW (hb : FiniteLowerBoundary n r) : CWComplex (Set.univ : Set (DiskAttachment r)) where
  cell := AttachmentCell (X := X) (J := J) n
  map := attachmentCharacteristic n r hr x₀
  source_eq m := by
    rintro (j | ⟨j, rfl⟩)
    · exact ClosedEmbeddingCW.imageCharacteristic_source _ _ m j
    · exact diskCharacteristic_source r x₀ j
  continuousOn m := by
    rintro (j | ⟨j, rfl⟩)
    · exact ClosedEmbeddingCW.imageCharacteristic_continuousOn _ _ m j
    · exact diskCharacteristic_continuousOn r x₀ j
  continuousOn_symm m := by
    rintro (j | ⟨j, rfl⟩)
    · exact ClosedEmbeddingCW.imageCharacteristic_continuousOn_symm _ _ m j
    · exact diskCharacteristic_continuousOn_symm r x₀ j
  pairwiseDisjoint' := by
    rintro ⟨m, i | ⟨i, hm⟩⟩ _ ⟨k, j | ⟨j, hk⟩⟩ _ hne
    · change Disjoint (attachmentCharacteristic n r hr x₀ m (.inl i) '' ball 0 1)
        (attachmentCharacteristic n r hr x₀ k (.inl j) '' ball 0 1)
      rw [attachmentCharacteristic_old_image, attachmentCharacteristic_old_image]
      refine Set.disjoint_left.mpr fun _ ⟨a, ha, ea⟩ ⟨b, hb, eb⟩ => ?_
      cases old_injective r (boundaryFamilyInclusion J (Fin n → ℝ)) (ea.trans eb.symm)
      exact Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne (C := (Set.univ : Set X))
        fun h => hne (congrArg (fun z : Σ m, RelCWComplex.cell (Set.univ : Set X) m =>
          (⟨z.1, Sum.inl z.2⟩ : Σ m, AttachmentCell (X := X) (J := J) n m)) h)) ha hb
    · subst k
      change Disjoint (attachmentCharacteristic n r hr x₀ m (.inl i) '' ball 0 1)
        (attachmentCharacteristic n r hr x₀ n (.inr ⟨j, rfl⟩) '' ball 0 1)
      rw [attachmentCharacteristic_new, attachmentCharacteristic_old_image]
      exact (diskCharacteristic_disjoint_old r x₀ j).symm.mono_left (Set.image_subset_range _ _)
    · subst m
      change Disjoint (attachmentCharacteristic n r hr x₀ n (.inr ⟨i, rfl⟩) '' ball 0 1)
        (attachmentCharacteristic n r hr x₀ k (.inl j) '' ball 0 1)
      rw [attachmentCharacteristic_new, attachmentCharacteristic_old_image]
      exact (diskCharacteristic_disjoint_old r x₀ i).mono_right (Set.image_subset_range _ _)
    · subst m; subst k
      change Disjoint (attachmentCharacteristic n r hr x₀ n (.inr ⟨i, rfl⟩) '' ball 0 1)
        (attachmentCharacteristic n r hr x₀ n (.inr ⟨j, rfl⟩) '' ball 0 1)
      rw [attachmentCharacteristic_new, attachmentCharacteristic_new]
      exact diskCharacteristic_disjoint r x₀ fun h => hne (h ▸ rfl)
  mapsTo' m := by
    rintro (j | ⟨j, rfl⟩)
    · obtain ⟨I, hI⟩ := Topology.CWComplex.mapsTo' (C := (Set.univ : Set X)) m j
      refine ⟨fun k => (I k).image Sum.inl, fun x hx => ?_⟩
      obtain ⟨k, hk, i, hi, hx'⟩ := by simpa only [Set.mem_iUnion] using hI hx
      refine Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hk, Set.mem_iUnion.mpr
        ⟨Sum.inl i, Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨i, hi, rfl⟩, ?_⟩⟩⟩⟩
      rw [attachmentCharacteristic_old_image]; exact ⟨RelCWComplex.map m j x, hx', rfl⟩
    · obtain ⟨I, hI⟩ := hb j
      refine ⟨fun k => (I k).image Sum.inl, fun x hx => ?_⟩
      have hx' : ‖x‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
      rw [attachmentCharacteristic_new, diskCharacteristic_boundary r x₀ j x hx']
      obtain ⟨k, hk, i, hi, ha⟩ := by simpa only [Set.mem_iUnion] using hI ⟨x, hx'⟩
      refine Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hk, Set.mem_iUnion.mpr
        ⟨Sum.inl i, Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨i, hi, rfl⟩, ?_⟩⟩⟩⟩
      rw [attachmentCharacteristic_old_image]; exact ⟨r ⟨j, ⟨x, hx'⟩⟩, ha, rfl⟩
  closed' S _ hS := by
    refine diskAttachment_isClosed r S
      ((CWComplex.closed (Set.univ : Set X) _ (Set.subset_univ _)).mpr fun m j => ?_) fun j => ?_
    · have hs := (hS m (Sum.inl j)).preimage (old_continuous r (boundaryFamilyInclusion J (Fin n → ℝ)))
      rw [attachmentCharacteristic_old_image] at hs
      simpa only [Set.preimage_inter, Set.preimage_image_eq _ (old_injective r _), RelCWComplex.closedCell] using hs
    · have hs := (hS n (Sum.inr ⟨j, rfl⟩)).preimage
        (f := fun x : ClosedUnitBall (Fin n → ℝ) => cell r (boundaryFamilyInclusion J (Fin n → ℝ)) ⟨j, x⟩)
        ((cell_continuous r (boundaryFamilyInclusion J (Fin n → ℝ))).comp continuous_sigmaMk)
      rw [attachmentCharacteristic_new, diskCharacteristic_closedCell] at hs
      rwa [show (fun x : ClosedUnitBall (Fin n → ℝ) => cell r (boundaryFamilyInclusion J (Fin n → ℝ)) ⟨j, x⟩) ⁻¹'
        (S ∩ Set.range (fun x : ClosedUnitBall (Fin n → ℝ) => cell r (boundaryFamilyInclusion J (Fin n → ℝ)) ⟨j, x⟩)) =
        (fun x : ClosedUnitBall (Fin n → ℝ) => cell r (boundaryFamilyInclusion J (Fin n → ℝ)) ⟨j, x⟩) ⁻¹' S from
        Set.ext fun x => and_iff_left ⟨x, rfl⟩] at hs
  union' := by
    refine Set.eq_univ_of_forall ?_
    rintro (x | d)
    · have hx : x ∈ ⋃ m, ⋃ j : RelCWComplex.cell (Set.univ : Set X) m,
          RelCWComplex.closedCell m j := by rw [CWComplex.union]; trivial
      obtain ⟨m, j, hx⟩ := by simpa only [Set.mem_iUnion] using hx
      refine Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨Sum.inl j, ?_⟩⟩
      rw [attachmentCharacteristic_old_image]; exact ⟨x, hx, rfl⟩
    · refine Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨Sum.inr ⟨d.val.1, rfl⟩, ?_⟩⟩
      rw [attachmentCharacteristic_new, diskCharacteristic_closedCell]
      exact ⟨d.val.2, cell_of_not_mem r _ d.val d.property⟩

variable (hb : FiniteLowerBoundary n r)

def attachmentOldSubcomplex :
    letI := attachmentCW n r hr x₀ hb
    CWComplex.Subcomplex (Set.univ : Set (DiskAttachment r)) := by
  letI := attachmentCW n r hr x₀ hb
  refine {
    carrier := Set.range (old r (boundaryFamilyInclusion J (Fin n → ℝ)))
    I := fun _ => Set.range Sum.inl
    closed' := (old_isClosedEmbedding r _ hr
      (boundaryFamilyInclusion_isClosedEmbedding J (Fin n → ℝ))).isClosed_range
    union' := ?_ }
  rw [Set.empty_union]; ext z; constructor
  · intro hz
    obtain ⟨m, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨⟨_, j, rfl⟩, hz⟩ := Set.mem_iUnion.mp hz
    change z ∈ attachmentCharacteristic n r hr x₀ m (Sum.inl j) '' ball 0 1 at hz
    rw [attachmentCharacteristic_old_image] at hz
    obtain ⟨y, _, rfl⟩ := hz; exact ⟨y, rfl⟩
  · rintro ⟨x, rfl⟩
    have hx : x ∈ ⋃ m, ⋃ j : RelCWComplex.cell (Set.univ : Set X) m,
        RelCWComplex.openCell m j := by rw [CWComplex.iUnion_openCell_eq_complex]; trivial
    obtain ⟨m, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨⟨Sum.inl j, ⟨j, rfl⟩⟩, ?_⟩⟩
    change old r _ x ∈ attachmentCharacteristic n r hr x₀ m (Sum.inl j) '' ball 0 1
    rw [attachmentCharacteristic_old_image]; exact ⟨x, hx, rfl⟩

def attachmentOldCellEquiv (m : ℕ) :
    RelCWComplex.cell (Set.univ : Set X) m ≃
      {j : AttachmentCell (X := X) (J := J) n m // j ∈ Set.range Sum.inl} where
  toFun j := ⟨Sum.inl j, ⟨j, rfl⟩⟩
  invFun := by rintro ⟨j | j, hk⟩; exacts [j, False.elim (by obtain ⟨_, h⟩ := hk; cases h)]
  left_inv _ := rfl
  right_inv := by rintro ⟨_, j, rfl⟩; rfl

theorem attachment_old_openCell (m : ℕ) (j : RelCWComplex.cell (Set.univ : Set X) m) :
    letI := attachmentCW n r hr x₀ hb
    old r (boundaryFamilyInclusion J (Fin n → ℝ)) '' CWComplex.openCell m j =
      CWComplex.openCell (C := (Set.univ : Set (DiskAttachment r))) m
        (attachmentOldCellEquiv (X := X) (J := J) n m j).val :=
  (attachmentCharacteristic_old_image n r hr x₀ m j (ball 0 1)).symm
