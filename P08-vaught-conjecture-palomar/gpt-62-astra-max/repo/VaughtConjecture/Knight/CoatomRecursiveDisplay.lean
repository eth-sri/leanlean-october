/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoatomRecursiveInput
public import VaughtConjecture.Knight.CanonicalRecursiveTopSections

/-! # History-free joint displays on the actual recursive coatom output

The given labels are glued on the literal shared inventory, then extended by
the constructed section operator. This does not combine two independent
cap histories. Truncation at a limit stage fixes every given face label.
-/

@[expose] public section

namespace VaughtConjecture.Knight.CoatomRecursiveDisplay
open AmalgamationPlan AmalgamatedBoundaryPlan SemSchemeBoundaryInput
open Transform Value ExtOrd CoatomRecursiveInput
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {s : Step A}
variable {m n : ℕ} (I : Input s m (n + 1) (n + 1))

abbrev boundary := (core I).original
abbrev left (d : Cell I.left.scheme) := boundary I (I.leftFace.map d)
abbrev right (d : Cell I.right.scheme) := boundary I (I.rightFace.map d)

/-- The literal-top section theorem now covers the entire output inventory. -/
theorem extend_boundary {p} (hp : RespectsSemantics I.rows p) :
    ∃ r, RespectsSemantics (rows I) r ∧
      ∀ d, r (boundary I d) = p d := by
  have oldGrade (d : Cell I.boundary) : I.boundary.grade d ≤ n + 1 := 
    OrdinaryRawScope.boundary_grade I.rows (raw I) (card_eq I).le d
  let all (d : Cell (scheme I)) : (scheme I).below (A, n + 1) :=
    ⟨d, (scheme I).isPlan.subset_of_mem ((scheme I).scope_mem_plan d), (core I).grade d⟩
  obtain ⟨r, hr, he⟩ := CanonicalRecursiveTopSections.exists_section I.rows (raw I).proper
    (n + 1) (height_le I) (hp.toBelow (A, n + 1))
  refine ⟨fun d => r (all d), hr.toRespects (fun d => (all d).2), ?_⟩
  intro d
  exact he ⟨d, I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan d), oldGrade d⟩

theorem joint_section {p} {q}
    (hp : RespectsSemantics I.left.rows p) (hq : RespectsSemantics I.right.rows q)
    (ha : ∀ i, p (I.shared.f i) = q (I.shared.g i)) :
    ∃ r, RespectsSemantics (rows I) r ∧
      (∀ d, r (left I d) = p d) ∧ ∀ d, r (right I d) = q d := by
  obtain ⟨r, hr, he⟩ := extend_boundary I (I.paste_respects hp hq ha)
  exact ⟨r, hr, fun d => (he _).trans (I.paste_left _ _ d),
    fun d => (he _).trans (I.paste_right _ _ ha d)⟩

/-- Stage bounding changes only newly supplied labels. Both complete input
faces, including literal tops, remain unchanged. -/
theorem joint_bounded {α} (hα : Order.IsSuccLimit α)
    {p} {q}
    (hp : RespectsSemantics I.left.rows p) (hq : RespectsSemantics I.right.rows q)
    (hpb : ∀ d, p d < ofOrd α ∨ p d = ⊤) (hqb : ∀ d, q d < ofOrd α ∨ q d = ⊤)
    (ha : ∀ i, p (I.shared.f i) = q (I.shared.g i)) :
    ∃ r, RespectsSemantics (rows I) r ∧
      (∀ d, r d < ofOrd α ∨ r d = ⊤) ∧
      (∀ d, r (left I d) = p d) ∧ ∀ d, r (right I d) = q d := by
  obtain ⟨r, hr, hl, hright⟩ := joint_section I hp hq ha
  refine ⟨fun d => truncExt α (r d), hr.truncate hα, fun d => truncExt_bound α _, ?_, ?_⟩
  · intro d
    change truncExt α (r (left I d)) = p d
    rw [hl]
    exact truncExt_id_of_bound (hpb d)
  · intro d
    change truncExt α (r (right I d)) = q d
    rw [hright]
    exact truncExt_id_of_bound (hqb d)

private theorem faceMap_label {α} {a b}
    p (r : S α a) (f : Fin a ↪ Fin b)
    (hv : Finset.univ.image f ∈ p.scheme.scheme.plan)
    (hs : p.scheme.restrictFace f hv = r.scheme) (h : typeMap f p = some r)
    d :
    p.label (SemSchemeBoundaryInput.faceMap p.scheme r.scheme f hv hs d) = r.label d := by
  have he := Option.some.inj ((typeMap_eq_some f p hv).symm.trans h)
  subst r
  rfl

/-- Compatibility of stage types supplies literal label agreement as well
as the shared scheme. No extra overlap-label equation is requested. -/
theorem compatible_labels {α} (C : CoatomPair n)
    {pa pb : S α (n + 1)} (h : C.Compatible pa pb) :
    let I := (CoatomBoundaryPresentation.of_compatible C h).input
    ∀ i, pa.label (I.shared.f i) = pb.label (I.shared.g i) := by
  dsimp
  intro i
  let r := Classical.choose h
  have hl := (Classical.choose_spec h).1
  exact (faceMap_label pa r C.g₁ _ _ hl i).trans (faceMap_label pb r C.g₂ _ _ (Classical.choose_spec h).2 i).symm

end
end VaughtConjecture.Knight.CoatomRecursiveDisplay
