module

public import RequestProject.AttachmentHomotopyExtension

@[expose] public section

/-! Continuous pasting on the two ends and the side of a cylinder.
The side is any closed subspace, including an arbitrary disjoint family of
disk boundaries. -/

noncomputable section

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u v
variable {D : Type u} [TopologicalSpace D] (S : Set D)

abbrev FullCylinderBoundary :=
  {z : I × D // z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ S}

variable {Z : Type v} [TopologicalSpace Z]

/-- Pasting on the two closed ends and closed side of the cylinder. -/
def fullCylinderPasting (hS : IsClosed S) (f₀ f₁ : C(D, Z)) (H : C(I × S, Z))
    (h₀ : ∀ x, H (0, x) = f₀ x.val) (h₁ : ∀ x, H (1, x) = f₁ x.val) :
    C(FullCylinderBoundary S, Z) :=
  (cylinderPasting (T := {0, 1}) (S := S)
    ⟨fun z => (if z.1.val = 0 then f₀ else f₁) z.2,
      by
        let : Finite (↑({0, 1} : Set I)) := (Set.finite_singleton 1).insert 0 |>.to_subtype
        exact continuous_prod_of_discrete_left.mpr fun t => (if t.val = 0 then f₀ else f₁).continuous⟩
    H (by rw [Set.insert_eq]; exact isClosed_singleton.union isClosed_singleton) hS (by
      rintro ⟨t, ht | ht⟩ x
      · simpa [show t = 0 from ht] using (h₀ x).symm
      · simpa [show t = 1 from ht, one_ne_zero] using (h₁ x).symm)).comp
      ⟨fun z => ⟨z.val, or_assoc.mpr z.property⟩, continuous_subtype_val.subtype_mk _⟩

theorem fullCylinderPasting_end (hS : IsClosed S) (f₀ f₁ : C(D, Z))
    (H : C(I × S, Z)) (h₀ : ∀ x, H (0, x) = f₀ x.val)
    (h₁ : ∀ x, H (1, x) = f₁ x.val) (t : I) (ht : t = 0 ∨ t = 1) (d : D) :
    fullCylinderPasting S hS f₀ f₁ H h₀ h₁ ⟨(t, d), ht.imp id Or.inl⟩ =
      (if t = 0 then f₀ else f₁) d := by
  rw [fullCylinderPasting, ContinuousMap.comp_apply, cylinderPasting_slice _ ht]
  rfl

@[simp] theorem fullCylinderPasting_side (hS : IsClosed S) (f₀ f₁ : C(D, Z))
    (H : C(I × S, Z)) (h₀ : ∀ x, H (0, x) = f₀ x.val)
    (h₁ : ∀ x, H (1, x) = f₁ x.val) (t : I) (x : S) :
    fullCylinderPasting S hS f₀ f₁ H h₀ h₁
      ⟨(t, x.val), Or.inr (Or.inr x.property)⟩ = H (t, x) :=
  by
    rw [fullCylinderPasting, ContinuousMap.comp_apply]
    apply cylinderPasting_side

end FiniteChains.RelativeAttachment
