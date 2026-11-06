import RequestProject.HomeomorphContinuousMap
import RequestProject.PointAttachmentHomotopyEquiv
import RequestProject.AttachmentQuotientHomeomorph


/-! Fill an attached pointed circle (or, more generally, a pointed
boundary space) by its disk. The resulting iterated attachment is
homeomorphic to attaching the disk at the single marked boundary point.
This is an actual quotient argument, preserving every old point. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open Topology
open scoped Topology

universe u
variable {X C S D : Type u} [TopologicalSpace X] [TopologicalSpace C]
  [TopologicalSpace S] [TopologicalSpace D]
  (x : X) (c : C) (b : S ≃ₜ C) (i : C(S, D)) (hi : Function.Injective i)

def pointFillAttaching := (pointCell x c).comp b.toContinuousMap

abbrev FilledPointAttachment := Space (pointFillAttaching x c b) i

def pointFillBase : C(X, FilledPointAttachment x c b i) :=
  (⟨old _ i, old_continuous _ _⟩ :
    C(PointAttachment x c, _)).comp (pointOld x c)

def pointFillDisk : C(D, FilledPointAttachment x c b i) :=
  ⟨cell _ i, cell_continuous _ _⟩

include hi in
theorem pointFillDisk_boundary (a : S) :
    pointFillDisk x c b i (i a) = old (pointFillAttaching x c b) i (pointCell x c (b a)) :=
  cell_boundary _ _ hi a

include hi in
theorem pointFillDisk_circle (y : C) :
    pointFillDisk x c b i (i (b.symm y)) = old (pointFillAttaching x c b) i (pointCell x c y) := by
  rw [pointFillDisk_boundary x c b i hi, Homeomorph.apply_symm_apply]

include hi in
theorem pointFillDisk_mark :
    pointFillDisk x c b i (i (b.symm c)) = pointFillBase x c b i x := by
  rw [pointFillDisk_circle x c b i hi, pointCell_mark]
  rfl

theorem pointFillBase_injective : Function.Injective (pointFillBase x c b i) :=
  (old_injective _ _).comp (old_injective _ _)

theorem pointFillDisk_injective : Function.Injective (pointFillDisk x c b i) :=
  attachmentCell_injective _ _ ((pointCell_injective x c).comp b.injective)

include hi in
theorem pointFillDisk_mem_base_iff (d : D) :
    pointFillDisk x c b i d ∈ Set.range (pointFillBase x c b i) ↔ d = i (b.symm c) := by
  have hrange : Set.range (pointFillBase x c b i) =
      old _ i '' Set.range (pointOld x c) := by
    aesop
  rw [hrange]
  change d ∈ cell _ i ⁻¹'
    (old _ i '' Set.range (pointOld x c)) ↔ _
  rw [cell_preimage_old_image _ _ hi]
  constructor
  · rintro ⟨a, ha, had⟩
    have hac := (pointCell_mem_old_iff x c _).mp ha
    aesop
  · intro hd
    refine ⟨b.symm c, ?_, hd.symm⟩
    apply (pointCell_mem_old_iff x c _).mpr
    exact b.apply_symm_apply c

include hi in
theorem pointFill_piece_isQuotientMap :
    IsQuotientMap (Sum.elim (pointFillBase x c b i) (pointFillDisk x c b i)) := by
  apply isQuotientMap_iff_isClosed.mpr
  constructor
  · intro z
    obtain ⟨z, rfl⟩ := quotientMap_surjective _ i z
    cases z with
    | inl y =>
        obtain ⟨y, rfl⟩ := quotientMap_surjective (fun _ : PUnit => x) (fun _ : PUnit => c) y
        cases y with
        | inl t => tauto
        | inr a => exact ⟨Sum.inr (i (b.symm a)), pointFillDisk_circle x c b i hi a⟩
    | inr d => aesop
  · intro T
    constructor
    · exact fun hT => hT.preimage (by fun_prop)
    · intro hT
      have hX := hT.preimage (continuous_inl : Continuous (Sum.inl : X → X ⊕ D))
      have hD := hT.preimage (continuous_inr : Continuous (Sum.inr : D → X ⊕ D))
      apply isClosed_coinduced.mpr
      apply isClosed_sum_iff.mpr
      constructor
      · apply isClosed_coinduced.mpr
        apply isClosed_sum_iff.mpr
        constructor
        · exact hX
        · have hc := hD.preimage (i.continuous.comp b.symm.continuous)
          convert hc using 1
          ext y
          exact iff_of_eq (congrArg (· ∈ T) (pointFillDisk_circle x c b i hi y).symm)
      · exact hD

/-- The two-stage pointed-boundary filling is literally a disk attached
at one point, with exact base and disk formulas. -/
def pointAttachmentFillingHomeomorph :
    PointAttachment x (i (b.symm c)) ≃ₜ FilledPointAttachment x c b i :=
  attachmentQuotientHomeomorph (fun _ : PUnit => x) (fun _ : PUnit => i (b.symm c))
    (pointFillBase x c b i) (pointFillDisk x c b i)
    (fun _ => (pointFillDisk_mark x c b i hi).symm)
    (pointFillBase_injective x c b i)
    (fun d => by
      simp [pointFillDisk_mem_base_iff x c b i hi])
    (fun _ _ _ _ h => pointFillDisk_injective x c b i h)
    (pointFill_piece_isQuotientMap x c b i hi)

@[simp] theorem pointAttachmentFillingHomeomorph_old y :
    pointAttachmentFillingHomeomorph x c b i hi (pointOld x (i (b.symm c)) y) =
      pointFillBase x c b i y := attachmentQuotientHomeomorph_old ..


variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

def pointBoundaryFillingHomotopyEquiv (b : UnitBoundary E ≃ₜ C) :=
  (pointBallAttachmentHomotopyEquiv x _).trans
    (pointAttachmentFillingHomeomorph x c b (unitBoundaryInclusion E)
      (fun _ _ h => Subtype.ext (congrArg (·.val) h))).toHomotopyEquiv

