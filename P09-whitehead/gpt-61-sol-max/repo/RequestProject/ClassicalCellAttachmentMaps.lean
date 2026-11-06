import Mathlib.Tactic

import RequestProject.ClosedEmbeddingCWImage
import RequestProject.BallHomotopyExtension

/-! Characteristic maps for an arbitrary family of genuine disks attached
to a literal old space. The norm may be the sup norm used by classical CW
structures. No finiteness of the family is assumed. Pending Lean verification.
-/

noncomputable section

open Set Topology

namespace FiniteChains.RelativeAttachment

variable (J E : Type u) [NormedAddCommGroup E]

abbrev DiskFamily := Σ _ : J, ClosedUnitBall E
abbrev BoundaryFamily := Σ _ : J, UnitBoundary E

def boundaryFamilyInclusion : BoundaryFamily J E → DiskFamily J E :=
  fun a => ⟨a.1, unitBoundaryInclusion E a.2⟩

theorem boundaryFamilyInclusion_range (d : DiskFamily J E) :
    d ∈ Set.range (boundaryFamilyInclusion J E) ↔ ‖d.2.val‖ = 1 := by
  constructor
  · rintro ⟨⟨j, a⟩, rfl⟩
    exact a.property
  · aesop

theorem boundaryFamilyInclusion_isClosedEmbedding :
    IsClosedEmbedding (boundaryFamilyInclusion J E) := by
  constructor
  · change IsEmbedding (Sigma.map
      (β₁ := fun _ : J => UnitBoundary E) (β₂ := fun _ : J => ClosedUnitBall E) id
      (fun _ : J => (unitBoundaryInclusion E : UnitBoundary E → ClosedUnitBall E)))
    apply (isEmbedding_sigmaMap Function.injective_id).mpr
    intro j
    exact IsEmbedding.inclusion (fun _ h => h.le)
  · apply isClosed_sigma_iff.mpr
    intro j
    have he : (Sigma.mk j) ⁻¹' Set.range (boundaryFamilyInclusion J E) =
        {x : ClosedUnitBall E | ‖x.val‖ = 1} := by
      grind [boundaryFamilyInclusion_range]
    rw [he]
    exact isClosed_eq (continuous_norm.comp continuous_subtype_val) continuous_const

variable {J E}
variable {X : Type u} [TopologicalSpace X]
  (r : BoundaryFamily J E → X) (x₀ : X)

abbrev DiskAttachment := Space r (boundaryFamilyInclusion J E)

variable (j : J)
/-- A total characteristic function; only its values on the closed ball
are used. Outside the disk it takes the chosen old value. -/
def diskCharacteristicFun  (x : E)  :=
  if hx : ‖x‖ ≤ 1 then cell r (boundaryFamilyInclusion J E) ⟨j, ⟨x, hx⟩⟩
  else old r (boundaryFamilyInclusion J E) x₀

omit [TopologicalSpace X] in
theorem diskCharacteristicFun_closed  (x : E) (hx : ‖x‖ ≤ 1) :
    diskCharacteristicFun r x₀ j x =
      cell r (boundaryFamilyInclusion J E) ⟨j, ⟨x, hx⟩⟩ := by
  simp_all [diskCharacteristicFun]

variable (x : {x : E // ‖x‖ < 1})
def interiorDiskPoint   :
    {d : DiskFamily J E // d ∉ Set.range (boundaryFamilyInclusion J E)} :=
  ⟨⟨j, ⟨x.val, x.property.le⟩⟩, fun h =>
    (ne_of_lt x.property) ((boundaryFamilyInclusion_range J E _).mp h)⟩

theorem interiorDiskPoint_isEmbedding  : IsEmbedding (interiorDiskPoint (E := E) j) := by
  apply IsEmbedding.subtypeVal.of_comp_iff.mp
  
  exact IsEmbedding.sigmaMk.comp (IsEmbedding.inclusion
    (fun (x : E) (h : ‖x‖ < 1) => le_of_lt h))

theorem interiorDiskPoint_isOpenEmbedding  :
    IsOpenEmbedding (interiorDiskPoint (E := E) j) := by
  apply IsOpenEmbedding.of_comp (interiorDiskPoint (E := E) j)
    (boundaryFamilyInclusion_isClosedEmbedding J E).isClosed_range.isOpen_compl.isOpenEmbedding_subtypeVal
  
  exact IsOpenEmbedding.sigmaMk.comp (IsOpenEmbedding.inclusion
    (fun (x : E) (h : ‖x‖ < 1) => le_of_lt h)
    (isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const))

omit [TopologicalSpace X] in
theorem diskCharacteristicFun_interior   :
    diskCharacteristicFun r x₀ j x.val =
      fresh r (boundaryFamilyInclusion J E) (interiorDiskPoint j x) := by
  rw [diskCharacteristicFun_closed r x₀ j x.val x.property.le]
  exact cell_of_not_mem r _ _ (interiorDiskPoint j x).property

abbrev diskCharacteristicFun_restrict_isEmbedding   :=
  have he :=
    funext fun (x : { x : E // ‖x‖ < 1 }) => FiniteChains.RelativeAttachment.diskCharacteristicFun_interior r x₀ j x;
  Eq.mpr
    (id
      (congrArg
        (fun (_a : { x : E // ‖x‖ < 1 } → FiniteChains.RelativeAttachment.DiskAttachment r) => Topology.IsEmbedding _a)
        he))
    (Topology.IsEmbedding.comp
      (Topology.IsOpenEmbedding.isEmbedding
        (FiniteChains.RelativeAttachment.fresh_isOpenEmbedding r
          (FiniteChains.RelativeAttachment.boundaryFamilyInclusion J E)
          (FiniteChains.RelativeAttachment.boundaryFamilyInclusion_isClosedEmbedding J E).isClosed_range))
      (FiniteChains.RelativeAttachment.interiorDiskPoint_isEmbedding j))

theorem diskCharacteristicFun_injOn  :
    Set.InjOn (diskCharacteristicFun r x₀ j) {x : E | ‖x‖ < 1} := by
  intro x hx y hy hxy
  exact congrArg Subtype.val
    ((diskCharacteristicFun_restrict_isEmbedding r x₀ j).injective
      (show diskCharacteristicFun r x₀ j (⟨x, hx⟩ : {x : E // ‖x‖ < 1}).val =
        diskCharacteristicFun r x₀ j (⟨y, hy⟩ : {x : E // ‖x‖ < 1}).val from hxy))

/-- The partial equivalence required by the classical CW definition. -/
def diskCharacteristic   :=
  (diskCharacteristicFun_injOn r x₀ j).toPartialEquiv
    (diskCharacteristicFun r x₀ j) {x : E | ‖x‖ < 1}

theorem diskCharacteristic_source  :
    (diskCharacteristic r x₀ j).source = Metric.ball 0 1 := by
  aesop

theorem diskCharacteristic_continuousOn  :
    ContinuousOn (diskCharacteristic r x₀ j) (Metric.closedBall 0 1) := by
  apply continuousOn_iff_continuous_restrict.mpr
  change Continuous (fun x : Metric.closedBall (0 : E) 1 => diskCharacteristic r x₀ j x.val)
  have he : (fun x : Metric.closedBall (0 : E) 1 => diskCharacteristic r x₀ j x.val) =
      fun x : Metric.closedBall (0 : E) 1 =>
        cell r (boundaryFamilyInclusion J E)
          ⟨j, ⟨x.val, by aesop⟩⟩ := by
    funext x
    exact diskCharacteristicFun_closed r x₀ j x.val
      (by aesop)
  rw [he]
  exact (cell_continuous r (boundaryFamilyInclusion J E)).comp
    (continuous_sigmaMk.comp (continuous_subtype_val.subtype_mk _))

theorem diskCharacteristic_continuousOn_symm  :
    ContinuousOn (diskCharacteristic r x₀ j).symm (diskCharacteristic r x₀ j).target := by
  have ht : (diskCharacteristic r x₀ j).target =
      (fun x : {x : E // ‖x‖ < 1} => diskCharacteristicFun r x₀ j x.val) '' Set.univ := by
    aesop
  rw [ht]
  apply (diskCharacteristicFun_restrict_isEmbedding r x₀ j).isInducing.continuousOn_image_iff.mpr
  have he : (diskCharacteristic r x₀ j).symm ∘
      (fun x : {x : E // ‖x‖ < 1} => diskCharacteristicFun r x₀ j x.val) =
      (Subtype.val : {x : E // ‖x‖ < 1} → E) := by
    funext x
    exact (diskCharacteristic r x₀ j).left_inv x.property
  rw [he]
  exact continuous_subtype_val.continuousOn

theorem diskCharacteristic_boundary  (x : E) (hx : ‖x‖ = 1) :
    diskCharacteristic r x₀ j x =
      old r (boundaryFamilyInclusion J E) (r ⟨j, ⟨x, hx⟩⟩) := by
  rw [show diskCharacteristic r x₀ j x =
      cell r (boundaryFamilyInclusion J E) ⟨j, ⟨x, hx.le⟩⟩ from
        diskCharacteristicFun_closed r x₀ j x hx.le]
  exact cell_boundary r (boundaryFamilyInclusion J E)
    (boundaryFamilyInclusion_isClosedEmbedding J E).injective ⟨j, ⟨x, hx⟩⟩

theorem diskCharacteristic_openCell  :
    diskCharacteristic r x₀ j '' Metric.ball 0 1 =
      Set.range (fresh r (boundaryFamilyInclusion J E) ∘ interiorDiskPoint j) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ‖x‖ < 1 := by
      simp_all
    exact ⟨⟨x, hx'⟩, (diskCharacteristicFun_interior r x₀ j ⟨x, hx'⟩).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨x.val, ?_, diskCharacteristicFun_interior r x₀ j x⟩
    simpa [Metric.mem_ball, dist_zero_right] using x.property

theorem diskCharacteristic_closedCell  :
    diskCharacteristic r x₀ j '' Metric.closedBall 0 1 =
      Set.range (fun x : ClosedUnitBall E => cell r (boundaryFamilyInclusion J E) ⟨j, x⟩) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ‖x‖ ≤ 1 := by
      simp_all
    exact ⟨⟨x, hx'⟩, (diskCharacteristicFun_closed r x₀ j x hx').symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨x.val, ?_, diskCharacteristicFun_closed r x₀ j x.val x.property⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using x.property

theorem diskCharacteristic_disjoint_old  :
    Disjoint (diskCharacteristic r x₀ j '' Metric.ball 0 1)
      (Set.range (old r (boundaryFamilyInclusion J E))) := by
  grind [diskCharacteristic_openCell, old_fresh_disjoint]

theorem diskCharacteristic_disjoint {j k : J} (hjk : j ≠ k) :
    Disjoint (diskCharacteristic r x₀ j '' Metric.ball 0 1)
      (diskCharacteristic r x₀ k '' Metric.ball 0 1) := by
  rw [diskCharacteristic_openCell, diskCharacteristic_openCell]
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  have hd  := Sum.inr_injective hy
  exact hjk (congrArg (fun d => d.val.1) hd).symm

/-- The weak topology is exactly the topology of the old part and the
individual attached closed disks, including infinitely many disks. -/
theorem diskAttachment_isClosed (S : Set (DiskAttachment r))
    (hOld : IsClosed ((old r (boundaryFamilyInclusion J E)) ⁻¹' S))
    (hDisk : ∀ j, IsClosed ((fun x : ClosedUnitBall E =>
      cell r (boundaryFamilyInclusion J E) ⟨j, x⟩) ⁻¹' S)) : IsClosed S := by
  apply isClosed_coinduced.mpr
  apply isClosed_sum_iff.mpr
  refine ⟨hOld, ?_⟩
  exact isClosed_sigma_iff.mpr hDisk

end FiniteChains.RelativeAttachment
