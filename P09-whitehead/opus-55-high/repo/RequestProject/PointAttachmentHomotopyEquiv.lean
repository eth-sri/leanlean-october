import RequestProject.HomeomorphContinuousMap
import RequestProject.AttachmentBaseChange
import RequestProject.BallHomotopyExtension
import RequestProject.Tac


/-! Attaching a contractible pointed space at one old point preserves
the homotopy type by an explicit contraction. This is the geometric
ingredient for adding a dummy generator together with its killing disk. -/

noncomputable section
bwd

namespace FiniteChains.RelativeAttachment
open Topology
open scoped Classical unitInterval Topology

universe u
variable {A X D : Type u} [TopologicalSpace X] [TopologicalSpace D]

theorem attachmentQuotientMap_isQuotientMap (r : A → X) (i : A → D) :
    IsQuotientMap (quotientMap r i) :=
  ⟨⟨rfl⟩, quotientMap_surjective r i⟩

omit [TopologicalSpace X] [TopologicalSpace D] in
/-- Injectivity of the attaching map keeps the entire disk embedded,
including its boundary. -/
theorem attachmentCell_injective (r : A → X) (i : A → D) (hr : Function.Injective r) :
    Function.Injective (cell r i) := by
  intro d e h
  by_cases hd : d ∈ Set.range i
  · by_cases he : e ∈ Set.range i
    · grind [cell]
    · simp_all [cell, dif_neg he]
  · by_cases he : e ∈ Set.range i
    · simp_all [cell, dif_pos he]
    · grind [cell]

omit [TopologicalSpace X] [TopologicalSpace D] in
theorem attachmentCell_mem_old_iff (r : A → X) (i : A → D) (d : D) :
    cell r i d ∈ Set.range (old r i) ↔ d ∈ Set.range i := by
  by_cases hd : d ∈ Set.range i
  · simp [cell]
    aesop
  · constructor
    · rintro ⟨x, hx⟩
      rw [cell_of_not_mem r i d hd] at hx
      tauto
    simp_all

abbrev PointAttachment (x : X) (d : D) :=
  Space (fun _ : PUnit => x) (fun _ : PUnit => d)

def pointOld (x : X) (d : D) : C(X, PointAttachment x d) :=
  ⟨old (fun _ : PUnit => x) (fun _ : PUnit => d), old_continuous _ _⟩

def pointCell (x : X) (d : D) : C(D, PointAttachment x d) :=
  ⟨cell (fun _ : PUnit => x) (fun _ : PUnit => d), cell_continuous _ _⟩

theorem pointCell_injective (x : X) (d : D) : Function.Injective (pointCell x d) :=
  attachmentCell_injective (fun _ => x) _
    (by tauto)

@[simp] theorem pointCell_mark (x : X) (d : D) : pointCell x d d = pointOld x d x :=
  cell_boundary (fun _ => x) _
    (fun _ _ _ => Subsingleton.elim _ _) PUnit.unit

theorem pointCell_mem_old_iff (x : X) (d c : D) :
    pointCell x d c ∈ Set.range (pointOld x d) ↔ c = d := by
  change cell _ _ c ∈
    Set.range (old _ _) ↔ c = d
  rw [attachmentCell_mem_old_iff]
  simp

def pointProjection (x : X) (d : D) : C(PointAttachment x d, X) :=
  desc (fun _ : PUnit => x) (fun _ : PUnit => d)
    (ContinuousMap.id X) (ContinuousMap.const D x) (by simp)


@[simp] theorem pointProjection_cell (x : X) (d c : D) :
    pointProjection x d (pointCell x d c) = x := desc_cell ..

def pointAttachmentContraction (x : X) d
    (H : (ContinuousMap.const D d).Homotopy (ContinuousMap.id D))
    (hfix : ∀ t, H (t, d) = d) :
    ((pointOld x d).comp (pointProjection x d)).Homotopy (ContinuousMap.id (PointAttachment x d)) := by
  let F : C(I × X, PointAttachment x d) := (pointOld x d).comp ⟨Prod.snd, continuous_snd⟩
  let G : C(I × D, PointAttachment x d) := (pointCell x d).comp H.toContinuousMap
  have hbd : ∀ t (a : PUnit), F (t, x) = G (t, d) := by
    intro t _a
    change pointOld x d x = pointCell x d (H (t, d))
    rw [hfix, pointCell_mark]
  let L := attachmentHomotopyPasting (fun _ : PUnit => x) (fun _ : PUnit => d) F G hbd
  refine { toContinuousMap := L, map_zero_left := ?_, map_one_left := ?_ }
  · intro z
    obtain ⟨z, rfl⟩ := quotientMap_surjective (fun _ : PUnit => x) (fun _ : PUnit => d) z
    cases z with
    | inl y => rfl
    | inr c =>
        change attachmentHomotopyPasting _ _ F G hbd (0, cell _ _ c) =
          pointOld x d (pointProjection x d (pointCell x d c))
        aesop
  · intro z
    obtain ⟨z, rfl⟩ := quotientMap_surjective (fun _ : PUnit => x) (fun _ : PUnit => d) z
    cases z with
    | inl y => rfl
    | inr c =>
        change attachmentHomotopyPasting _ _ F G hbd (1, cell _ _ c) = pointCell x d c
        aesop

def pointAttachmentOldHomotopyEquiv (x : X) d
    (H : (ContinuousMap.const D d).Homotopy (ContinuousMap.id D))
    (hfix : ∀ t, H (t, d) = d) : ContinuousMap.HomotopyEquiv X (PointAttachment x d) where
  toFun := pointOld x d
  invFun := pointProjection x d
  left_inv := ⟨ContinuousMap.Homotopy.refl (ContinuousMap.id X)⟩
  right_inv := ⟨pointAttachmentContraction x d H hfix⟩

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

def closedBallFromPointHomotopy (d : ClosedUnitBall E) :
    (ContinuousMap.const (ClosedUnitBall E) d).Homotopy (ContinuousMap.id (ClosedUnitBall E)) where
  toFun tx := ⟨(1 - (tx.1 : ℝ)) • d.val + (tx.1 : ℝ) • tx.2.val, by
    calc
      ‖(1 - (tx.1 : ℝ)) • d.val + (tx.1 : ℝ) • tx.2.val‖ ≤
          ‖(1 - (tx.1 : ℝ)) • d.val‖ + ‖(tx.1 : ℝ) • tx.2.val‖ := norm_add_le _ _
      _ = (1 - (tx.1 : ℝ)) * ‖d.val‖ + (tx.1 : ℝ) * ‖tx.2.val‖ := by
        grind [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr tx.1.property.2), Real.norm_of_nonneg tx.1.property.1]
      _ ≤ (1 - (tx.1 : ℝ)) * 1 + (tx.1 : ℝ) * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left d.property (sub_nonneg.mpr tx.1.property.2))
          (mul_le_mul_of_nonneg_left tx.2.property tx.1.property.1)
      _ = 1 := by ring⟩
  continuous_toFun := by
    fun_prop
  map_zero_left x := Subtype.ext (by simp)
  map_one_left x := Subtype.ext (by simp)

theorem closedBallFromPointHomotopy_fixed (d : ClosedUnitBall E) t :
    closedBallFromPointHomotopy d (t, d) = d := by
  apply Subtype.ext
  change (1 - (t : ℝ)) • d.val + (t : ℝ) • d.val = d.val
  rw [← add_smul, sub_add_cancel, one_smul]

def pointBallAttachmentHomotopyEquiv (x : X) (d : ClosedUnitBall E) :=
  pointAttachmentOldHomotopyEquiv x d _
    (closedBallFromPointHomotopy_fixed d)
