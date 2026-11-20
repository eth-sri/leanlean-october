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

variable (f₀ f₁ : C(D, Z)) (H : C(I × S, Z))

variable (z : FullCylinderBoundary S)

def fullCylinderPastingFun :=
  if h₀ : z.val.1 = 0 then f₀ z.val.2
  else if h₁ : z.val.1 = 1 then f₁ z.val.2
  else H (z.val.1, ⟨z.val.2, (z.property.resolve_left h₀).resolve_left h₁⟩)

theorem fullCylinderPastingFun_zero (hz : z.val.1 = 0) :
    fullCylinderPastingFun S f₀ f₁ H z = f₀ z.val.2 := by
  simp_all [fullCylinderPastingFun, dif_pos]

theorem fullCylinderPastingFun_one (hz : z.val.1 = 1) :
    fullCylinderPastingFun S f₀ f₁ H z = f₁ z.val.2 := by
  simp [hz, fullCylinderPastingFun, dif_neg, dif_pos]

theorem fullCylinderPastingFun_side
    (h₀ : ∀ x, H (0, x) = f₀ x.val) (h₁ : ∀ x, H (1, x) = f₁ x.val)
    (z : FullCylinderBoundary S) (hz : z.val.2 ∈ S) :
    fullCylinderPastingFun S f₀ f₁ H z = H (z.val.1, ⟨z.val.2, hz⟩) := by
  by_cases ht₀ : z.val.1 = 0
  · grind [fullCylinderPastingFun_zero]
  by_cases ht₁ : z.val.1 = 1
  · grind [fullCylinderPastingFun_one]
  simp only [fullCylinderPastingFun, dif_neg ht₀, dif_neg ht₁]

variable (hS : IsClosed S)
    (f₀ f₁ : C(D, Z))
    (H : C(I × S, Z))
    (h₀ : ∀ x, H (0, x) = f₀ x.val)
    (h₁ : ∀ x, H (1, x) = f₁ x.val)

/-- Pasting on the full cylinder boundary, with exact formulas on each of
the three closed pieces. -/
def fullCylinderPasting :
    C(FullCylinderBoundary S, Z) where
  toFun := fullCylinderPastingFun S f₀ f₁ H
  continuous_toFun := by
    let B₀ : Set (FullCylinderBoundary S) := {z | z.val.1 = 0}
    let B₁ : Set (FullCylinderBoundary S) := {z | z.val.1 = 1}
    let C : Set (FullCylinderBoundary S) := {z | z.val.2 ∈ S}
    have hb₀ : IsClosed B₀ := isClosed_eq (by fun_prop) continuous_const
    have hb₁ : IsClosed B₁ := isClosed_eq (by fun_prop) continuous_const
    have hcover : (B₀ ∪ B₁) ∪ C = Set.univ := by
      apply Set.eq_univ_of_forall
      intro z
      rcases z.property with h | h | h
      · solve_by_elim
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    have hf₀ : ContinuousOn (fullCylinderPastingFun S f₀ f₁ H) B₀ := by
      apply ((f₀.continuous.comp (continuous_snd.comp continuous_subtype_val)).continuousOn).congr
      solve_by_elim [fullCylinderPastingFun_zero]
    have hf₁ : ContinuousOn (fullCylinderPastingFun S f₀ f₁ H) B₁ := by
      apply ((f₁.continuous.comp (continuous_snd.comp continuous_subtype_val)).continuousOn).congr
      solve_by_elim [fullCylinderPastingFun_one]
    have hh : ContinuousOn (fullCylinderPastingFun S f₀ f₁ H) C := by
      rw [continuousOn_iff_continuous_restrict]
      let k : C(C, I × S) := {
        toFun := fun z => (z.val.val.1, ⟨z.val.val.2, z.property⟩)
        continuous_toFun := by fun_prop }
      have he : C.domRestrict (fullCylinderPastingFun S f₀ f₁ H) = H ∘ k := by
        funext z
        apply fullCylinderPastingFun_side <;> assumption
      rw [he]
      exact H.continuous.comp k.continuous
    rw [← continuousOn_univ, ← hcover]
    exact (hf₀.union_of_isClosed hf₁ hb₀ hb₁).union_of_isClosed hh (hb₀.union hb₁) (hS.preimage (continuous_snd.comp continuous_subtype_val))

variable (d : D)

@[simp] theorem fullCylinderPasting_zero :
    fullCylinderPasting S hS f₀ f₁ H h₀ h₁ ⟨(0, d), Or.inl rfl⟩ = f₀ d :=
  fullCylinderPastingFun_zero S f₀ f₁ H _ rfl

@[simp] theorem fullCylinderPasting_one :
    fullCylinderPasting S hS f₀ f₁ H h₀ h₁ ⟨(1, d), Or.inr (Or.inl rfl)⟩ = f₁ d :=
  fullCylinderPastingFun_one S f₀ f₁ H _ rfl

@[simp] theorem fullCylinderPasting_side (t : I) (x : S) :
    fullCylinderPasting S hS f₀ f₁ H h₀ h₁
      ⟨(t, x.val), Or.inr (Or.inr x.property)⟩ = H (t, x) :=
  fullCylinderPastingFun_side S f₀ f₁ H h₀ h₁ _ x.property

end FiniteChains.RelativeAttachment
