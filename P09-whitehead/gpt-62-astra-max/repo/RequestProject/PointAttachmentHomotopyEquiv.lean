module


public import RequestProject.AttachmentBaseChange


@[expose] public section

/-! Attaching a contractible pointed space at one old point preserves
the homotopy type by an explicit contraction. This is the geometric
ingredient for adding a dummy generator together with its killing disk. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.RelativeAttachment
open Topology
open scoped Classical unitInterval Topology

universe u
variable {A X D : Type u} [TopologicalSpace X] [TopologicalSpace D]

variable (r : A → X) (i : A → D)

theorem attachmentQuotientMap_isQuotientMap :
    IsQuotientMap (quotientMap r i) :=
  ⟨⟨rfl⟩, quotientMap_surjective r i⟩

omit [TopologicalSpace X] [TopologicalSpace D] in
/-- Injectivity of the attaching map keeps the entire disk embedded,
including its boundary. -/
theorem attachmentCell_injective (hr : Function.Injective r) :
    Function.Injective (cell r i) := by
  intro d e h
  by_cases hd : d ∈ Set.range i
  · by_cases he : e ∈ Set.range i
    · simp only [cell, dif_pos hd, dif_pos he] at h <;> grind
    · simp_all [cell, dif_pos, dif_neg]
  · by_cases he : e ∈ Set.range i
    · simp_all [cell, dif_neg, dif_pos]
    · simp only [cell, dif_neg hd, dif_neg he] at h <;> grind

omit [TopologicalSpace X] [TopologicalSpace D] in
theorem attachmentCell_mem_old_iff (d : D) :
    cell r i d ∈ Set.range (old r i) ↔ d ∈ Set.range i := by
  by_cases hd : d ∈ Set.range i
  · simp only [cell, dif_pos hd] <;> aesop
  · constructor
    · rintro ⟨x, hx⟩
      rw [cell_of_not_mem r i d hd] at hx
      exact (Sum.inl_ne_inr hx).elim
    · simp_all

variable (x : X)

variable (d : D)

abbrev PointAttachment :=
  Space (fun _ : PUnit => x) (fun _ : PUnit => d)

def pointOld : C(X, PointAttachment x d) :=
  ⟨old _ _, old_continuous _ _⟩

def pointCell : C(D, PointAttachment x d) :=
  ⟨cell _ _, cell_continuous _ _⟩

theorem pointCell_injective : Function.Injective (pointCell x d) :=
  attachmentCell_injective (fun _ : PUnit => x) _
    (fun _ _ _ => Subsingleton.elim _ _)

@[simp] theorem pointCell_mark : pointCell x d d = pointOld x d x :=
  cell_boundary (fun _ : PUnit => x) _
    (fun _ _ _ => Subsingleton.elim _ _) PUnit.unit

theorem pointCell_mem_old_iff (d c : D) :
    pointCell x d c ∈ Set.range (pointOld x d) ↔ c = d := by
  change cell _ _ c ∈
    Set.range (old (fun _ : PUnit => x) (fun _ : PUnit => d)) ↔ c = d
  rw [attachmentCell_mem_old_iff] <;> simp_all

variable (d : D)

def pointProjection :=
  desc _ (fun _ : PUnit => d)
    (ContinuousMap.id X) (ContinuousMap.const D x) (fun _ => rfl)

@[simp] theorem pointProjection_old (y : X) :
    pointProjection x d (pointOld x d y) = y := rfl

@[simp] theorem pointProjection_cell (d c : D) :
    pointProjection x d (pointCell x d c) = x := desc_cell ..

variable (d : D)
    (H : (ContinuousMap.const D d).Homotopy (ContinuousMap.id D))
    (hfix : ∀ t, H (t, d) = d)

def pointAttachmentContraction :
    ((pointOld x d).comp (pointProjection x d)).Homotopy (ContinuousMap.id (PointAttachment x d)) := by
  let F : C(I × X, PointAttachment x d) := (pointOld x d).comp ⟨Prod.snd, continuous_snd⟩
  let G := (pointCell x d).comp H.toContinuousMap
  have hbd : ∀ t (a : PUnit), F (t, x) = G (t, d) := by
    intro t _a
    change pointOld x d x = pointCell x d (H (t, d))
    rw [hfix, pointCell_mark]
  refine { toContinuousMap := attachmentHomotopyPasting _ _ F G hbd, map_zero_left := ?_, map_one_left := ?_ }
  · intro z
    obtain ⟨z, rfl⟩ := quotientMap_surjective _ _ z
    cases z with
    | inl y => rfl
    | inr c =>
        change attachmentHomotopyPasting _ _ F G hbd (0, cell _ _ c) =
          pointOld x d (pointProjection x d (pointCell x d c))
        aesop
  · intro z
    obtain ⟨z, rfl⟩ := quotientMap_surjective _ _ z
    cases z with
    | inl y => rfl
    | inr c =>
        change attachmentHomotopyPasting _ _ F G hbd (1, cell _ _ c) = pointCell x d c
        aesop

def pointAttachmentOldHomotopyEquiv : ContinuousMap.HomotopyEquiv X (PointAttachment x d) where
  toFun := pointOld x d
  invFun := pointProjection x d
  left_inv := ⟨ContinuousMap.Homotopy.refl _⟩
  right_inv := ⟨pointAttachmentContraction x d H hfix⟩

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable (d : ClosedUnitBall E)

def closedBallFromPointHomotopy :
    (ContinuousMap.const (ClosedUnitBall E) d).Homotopy (ContinuousMap.id (ClosedUnitBall E)) where
  toFun tx := ⟨(1 - (tx.1 : ℝ)) • d.val + (tx.1 : ℝ) • tx.2.val, by
    calc
      ‖(1 - (tx.1 : ℝ)) • d.val + (tx.1 : ℝ) • tx.2.val‖ ≤
          ‖(1 - (tx.1 : ℝ)) • d.val‖ + ‖(tx.1 : ℝ) • tx.2.val‖ := norm_add_le _ _
      _ = (1 - (tx.1)) * ‖d.val‖ + (tx.1) * ‖tx.2.val‖ := by
        grind [norm_smul, Real.norm_of_nonneg]
      _ ≤ (1 - (tx.1)) * 1 + (tx.1) * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left d.property (sub_nonneg.mpr tx.1.property.2))
          (mul_le_mul_of_nonneg_left tx.2.property tx.1.property.1)
      _ = 1 := by ring⟩
  continuous_toFun := by
    fun_prop
  map_zero_left x := Subtype.ext (by simp)
  map_one_left x := Subtype.ext (by simp)

theorem closedBallFromPointHomotopy_fixed (t : I) :
    closedBallFromPointHomotopy d (t, d) = d := by
  apply Subtype.ext
  change (1 - (t : ℝ)) • d.val + (t : ℝ) • d.val = d.val
  rw [← add_smul, sub_add_cancel, one_smul]

def pointBallAttachmentHomotopyEquiv (x : X) (d : ClosedUnitBall E) :=
  pointAttachmentOldHomotopyEquiv x d _
    (closedBallFromPointHomotopy_fixed d)

end FiniteChains.RelativeAttachment
