module

public import RequestProject.ClassicalCellAttachmentMaps
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open scoped Classical
open Set Topology Metric

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.ClassicalSkeletonAttachment
open RelativeAttachment

variable {X : Type} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]

abbrev SkeletonCarrier (n : ℕ) :=
  {x : X // x ∈ CWComplex.skeletonLT C (n : ℕ∞)}

def skeletonInclusion (n : ℕ) : C(SkeletonCarrier C n, SkeletonCarrier C (n + 1)) :=
  ⟨fun x => ⟨x.val, CWComplex.skeletonLT_mono (C := C)
    (by exact_mod_cast Nat.le_succ n) x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

def characteristicDisk (n : ℕ) (j : RelCWComplex.cell C n) :
    C(ClosedUnitBall (Fin n → ℝ), X) :=
  ⟨fun x => RelCWComplex.map n j x.val,
    (RelCWComplex.continuousOn n j).comp_continuous continuous_subtype_val fun x => by
      simpa only [Metric.mem_closedBall, dist_zero_right] using x.property⟩

def characteristicDiskFamily (n : ℕ) :
    C(DiskFamily (RelCWComplex.cell C n) (Fin n → ℝ), X) :=
  ⟨fun d => characteristicDisk C n d.1 d.2,
    continuous_sigma fun j => (characteristicDisk C n j).continuous⟩

def skeletonAttachingMap (n : ℕ) :
    C(BoundaryFamily (RelCWComplex.cell C n) (Fin n → ℝ), SkeletonCarrier C n) :=
  ⟨fun a => ⟨RelCWComplex.map n a.1 a.2.val,
      CWComplex.cellFrontier_subset_skeletonLT n a.1
        ⟨a.2.val, by simpa only [Metric.mem_sphere, dist_zero_right] using a.2.property, rfl⟩⟩,
    Continuous.subtype_mk ((characteristicDiskFamily C n).continuous.comp
      (boundaryFamilyInclusion_isClosedEmbedding (RelCWComplex.cell C n) (Fin n → ℝ)).continuous) _⟩

def skeletonAttachmentOrigin (n : ℕ) : C(DiskAttachment (skeletonAttachingMap C n), X) :=
  desc (skeletonAttachingMap C n)
    (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ))
    ⟨Subtype.val, continuous_subtype_val⟩ (characteristicDiskFamily C n) (fun _ => rfl)

@[simp] theorem skeletonAttachmentOrigin_cell (n : ℕ)
    (j : RelCWComplex.cell C n) (x : ClosedUnitBall (Fin n → ℝ)) :
    skeletonAttachmentOrigin C n
      (cell (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) ⟨j, x⟩) =
      RelCWComplex.map n j x.val := desc_cell ..

theorem skeletonAttachmentOrigin_injective (n : ℕ) :
    Function.Injective (skeletonAttachmentOrigin C n) := by
  have hnorm {d : DiskFamily (RelCWComplex.cell C n) (Fin n → ℝ)}
      (hd : d ∉ range (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ))) :
      ‖d.2.val‖ < 1 :=
    lt_of_le_of_ne d.2.property fun h => hd
      ((boundaryFamilyInclusion_range (RelCWComplex.cell C n) (Fin n → ℝ) d).mpr h)
  have hdisj (x : SkeletonCarrier C n) {k : RelCWComplex.cell C n}
      {y : ClosedUnitBall (Fin n → ℝ)} (hy : ⟨k, y⟩ ∉ range (boundaryFamilyInclusion _ _))
      (h : x.val = RelCWComplex.map n k y.val) : False :=
    Set.disjoint_left.mp (CWComplex.disjoint_skeletonLT_openCell (C := C) (j := k)
      (show (n : ℕ∞) ≤ n from le_rfl)) x.property
      (h.symm ▸ ⟨y.val, by simpa only [Metric.mem_ball, dist_zero_right] using hnorm hy, rfl⟩)
  rintro (x | ⟨⟨j, x⟩, hx⟩) (y | ⟨⟨k, y⟩, hy⟩) h
  · exact congrArg Sum.inl (Subtype.ext h)
  · exact (hdisj x hy h).elim
  · exact (hdisj y hx h.symm).elim
  · change RelCWComplex.map n j x.val = RelCWComplex.map n k y.val at h
    have hxlt := hnorm hx; have hylt := hnorm hy
    have hlabels : (⟨n, j⟩ : Σ m, RelCWComplex.cell C m) = ⟨n, k⟩ :=
      RelCWComplex.eq_of_not_disjoint_openCell fun hd => Set.disjoint_left.mp hd
        ⟨x.val, by simpa only [Metric.mem_ball, dist_zero_right] using hxlt, rfl⟩
        (h.symm ▸ ⟨y.val, by simpa only [Metric.mem_ball, dist_zero_right] using hylt, rfl⟩)
    cases eq_of_heq (Sigma.mk.inj_iff.mp hlabels).2
    have hxy : x.val = y.val := (RelCWComplex.map n j).injOn
      (by rw [RelCWComplex.source_eq]; simpa only [Metric.mem_ball, dist_zero_right] using hxlt)
      (by rw [RelCWComplex.source_eq]; simpa only [Metric.mem_ball, dist_zero_right] using hylt) h
    exact congrArg Sum.inr (Subtype.ext (congrArg (Sigma.mk j) (Subtype.ext hxy)))

theorem skeletonAttachmentOrigin_mem (n : ℕ)
    (z : DiskAttachment (skeletonAttachingMap C n)) :
    skeletonAttachmentOrigin C n z ∈ CWComplex.skeletonLT C (n + 1) := by
  obtain ⟨x | ⟨j, x⟩, rfl⟩ := quotientMap_surjective (skeletonAttachingMap C n)
    (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) z
  · exact CWComplex.skeletonLT_mono (C := C) (show (n : ℕ∞) ≤ n + 1 from le_self_add) x.property
  · change skeletonAttachmentOrigin C n (cell _ _ ⟨j, x⟩) ∈ _
    rw [skeletonAttachmentOrigin_cell]
    exact CWComplex.closedCell_subset_skeletonLT n j
      ⟨x.val, by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property, rfl⟩

def skeletonAttachmentMap (n : ℕ) :
    C(DiskAttachment (skeletonAttachingMap C n), SkeletonCarrier C (n + 1)) :=
  have hm (z) : skeletonAttachmentOrigin C n z ∈ CWComplex.skeletonLT C ((n + 1 : ℕ) : ℕ∞) := by
    simpa only [Nat.cast_add, Nat.cast_one] using skeletonAttachmentOrigin_mem C n z
  ⟨fun z => ⟨skeletonAttachmentOrigin C n z, hm z⟩,
    (skeletonAttachmentOrigin C n).continuous.subtype_mk hm⟩

theorem skeletonAttachmentOrigin_isClosedMap (n : ℕ) :
    IsClosedMap (skeletonAttachmentOrigin C n) := by
  intro A hA
  have hupper : skeletonAttachmentOrigin C n '' A ⊆ CWComplex.skeletonLT C (n + 1) := by
    rintro _ ⟨z, _, rfl⟩; exact skeletonAttachmentOrigin_mem C n z
  apply CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
    (hupper.trans (CWComplex.skeletonLT C (n + 1)).subset_complex)
  intro m _ j
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · right
    have hcell : CWComplex.closedCell m j ⊆ CWComplex.skeletonLT C (n : ℕ∞) :=
      (CWComplex.closedCell_subset_skeletonLT m j).trans
        (CWComplex.skeletonLT_mono (C := C) (by exact_mod_cast Nat.succ_le_of_lt hmn))
    have heq : skeletonAttachmentOrigin C n '' A ∩ CWComplex.closedCell m j =
        (Subtype.val '' (old (skeletonAttachingMap C n)
          (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) ⁻¹' A)) ∩
          CWComplex.closedCell m j := by
      ext x; constructor
      · rintro ⟨⟨z, hz, hzx⟩, hx⟩
        let b : SkeletonCarrier C n := ⟨x, hcell hx⟩
        have hzb : z = old _ _ b := skeletonAttachmentOrigin_injective C n hzx
        exact ⟨⟨b, show old _ _ b ∈ A from hzb ▸ hz, rfl⟩, hx⟩
      · rintro ⟨⟨b, hb, rfl⟩, hx⟩; exact ⟨⟨old _ _ b, hb, rfl⟩, hx⟩
    rw [heq]
    exact ((CWComplex.skeletonLT C (n : ℕ∞)).closed.isClosedMap_subtype_val _
      (hA.preimage (old_continuous _ _))).inter CWComplex.isClosed_closedCell
  · right
    subst m
    have heq : skeletonAttachmentOrigin C n '' A ∩ CWComplex.closedCell n j =
        characteristicDisk C n j '' ((fun x : ClosedUnitBall (Fin n → ℝ) =>
          cell (skeletonAttachingMap C n)
            (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) ⟨j, x⟩) ⁻¹' A) := by
      ext x; constructor
      · rintro ⟨⟨z, hz, hzx⟩, ⟨y, hy, hyx⟩⟩
        let d : ClosedUnitBall (Fin n → ℝ) :=
          ⟨y, by simpa only [Metric.mem_closedBall, dist_zero_right] using hy⟩
        exact ⟨d, show cell _ _ ⟨j, d⟩ ∈ A from
          (skeletonAttachmentOrigin_injective C n
            ((skeletonAttachmentOrigin_cell C n j d).trans (hyx.trans hzx.symm))).symm ▸ hz, hyx⟩
      · rintro ⟨d, hd, hdx⟩
        exact ⟨⟨cell _ _ ⟨j, d⟩, hd, (skeletonAttachmentOrigin_cell C n j d).trans hdx⟩,
          ⟨d.val, by simpa only [Metric.mem_closedBall, dist_zero_right] using d.property, hdx⟩⟩
    rw [heq]
    let : CompactSpace (ClosedUnitBall (Fin n → ℝ)) :=
      isCompact_iff_compactSpace.mp (by
        convert isCompact_closedBall (0 : Fin n → ℝ) 1 using 1
        ext x; simp only [Metric.mem_closedBall, dist_zero_right]; rfl)
    exact ((hA.preimage ((cell_continuous _ _).comp continuous_sigmaMk)).isCompact.image
      (characteristicDisk C n j).continuous).isClosed
  · left
    exact (CWComplex.disjoint_skeletonLT_openCell (C := C) (j := j)
      (show (n : ℕ∞) + 1 ≤ m by exact_mod_cast Nat.succ_le_of_lt hnm)).mono_left hupper

def skeletonAttachmentHomeomorph (n : ℕ) :
    DiskAttachment (skeletonAttachingMap C n) ≃ₜ SkeletonCarrier C (n + 1) :=
  (Equiv.ofBijective (skeletonAttachmentMap C n)
    ⟨fun _ _ h => skeletonAttachmentOrigin_injective C n (congrArg Subtype.val h), fun x => by
      have hx : x.val ∈ (CWComplex.skeletonLT C n : Set X) ∪
          ⋃ j : RelCWComplex.cell C n, CWComplex.closedCell n j := by
        rw [CWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ]
        simpa only [Nat.cast_add, Nat.cast_one] using
          (show x.val ∈ (CWComplex.skeletonLT C (n + 1) : Set X) from x.property)
      rcases hx with hx | hx
      · exact ⟨old _ _ ⟨x.val, hx⟩, Subtype.ext rfl⟩
      · obtain ⟨j, y, hy, hyx⟩ := Set.mem_iUnion.mp hx
        let d : ClosedUnitBall (Fin n → ℝ) :=
          ⟨y, by simpa only [Metric.mem_closedBall, dist_zero_right] using hy⟩
        exact ⟨cell _ _ ⟨j, d⟩, Subtype.ext ((skeletonAttachmentOrigin_cell C n j d).trans hyx)⟩⟩).toHomeomorphOfContinuousClosed
    (skeletonAttachmentMap C n).continuous fun A hA => by
      change IsClosed (skeletonAttachmentMap C n '' A)
      rw [show skeletonAttachmentMap C n '' A = Subtype.val ⁻¹' (skeletonAttachmentOrigin C n '' A) by
        ext x; constructor
        · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
        · rintro ⟨z, hz, hzx⟩; exact ⟨z, hz, Subtype.ext hzx⟩]
      exact (skeletonAttachmentOrigin_isClosedMap C n A hA).preimage continuous_subtype_val

def skeletonAsDiskAttachment (n : ℕ) :
    SkeletonCarrier C (n + 1) ≃ₜ DiskAttachment (skeletonAttachingMap C n) :=
  (skeletonAttachmentHomeomorph C n).symm

@[simp] theorem skeletonAttachmentHomeomorph_old_eq (n : ℕ) (x : SkeletonCarrier C n) :
    skeletonAttachmentHomeomorph C n
      (old (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) x) =
      skeletonInclusion C n x := rfl

@[simp] theorem skeletonAsDiskAttachment_inclusion (n : ℕ) (x : SkeletonCarrier C n) :
    skeletonAsDiskAttachment C n (skeletonInclusion C n x) =
      old (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) x := by
  rw [← skeletonAttachmentHomeomorph_old_eq C n x]
  exact (skeletonAttachmentHomeomorph C n).symm_apply_apply _

@[simp] theorem skeletonAttachmentHomeomorph_cell (n : ℕ)
    (j : RelCWComplex.cell C n) (x : ClosedUnitBall (Fin n → ℝ)) :
    (skeletonAttachmentHomeomorph C n
      (cell (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) ⟨j, x⟩)).val =
      RelCWComplex.map n j x.val := skeletonAttachmentOrigin_cell C n j x
