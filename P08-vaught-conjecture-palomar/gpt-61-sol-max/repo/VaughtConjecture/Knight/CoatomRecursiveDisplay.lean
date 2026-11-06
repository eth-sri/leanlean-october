import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CoatomRecursiveInput
import VaughtConjecture.Knight.CanonicalRecursiveTopSections
import VaughtConjecture.Knight.Coface

/-! # History-free joint displays on the actual recursive coatom output

The given labels are glued on the literal shared inventory, then extended by
the constructed section operator. This does not combine two independent
cap histories. Truncation at a limit stage fixes every given face label.
-/

namespace VaughtConjecture.Knight.CoatomRecursiveDisplay
open AmalgamationPlan AmalgamatedBoundaryPlan SemSchemeBoundaryInput
open  Value ExtOrd CoatomRecursiveInput
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {s : Step A}
variable {m n : ℕ} (I : Input s m (n + 3) (n + 3))

abbrev boundary := CanonicalRecursiveContract.boundary I.rows n (height_le I)
local notation "Cell₀" => Cell (scheme I)

abbrev left (d : Cell I.left.scheme) : Cell₀ :=
  boundary I (AmalgamatedBoundary.leftCell s I.leftScheme I.rightScheme I.shared
    I.planLeft I.planRight d)
abbrev right (d : Cell I.right.scheme) : Cell₀ :=
  boundary I (AmalgamatedBoundary.rightCell s I.leftScheme I.rightScheme I.shared
    I.planLeft I.planRight d)

/-- The literal-top section theorem now covers the entire output inventory. -/
theorem extend_boundary {p} (hp : RespectsSemantics I.rows p) :
    ∃ r , RespectsSemantics (rows I) r ∧
      ∀ d, r (boundary I d) = p d := by
  have oldGrade (d : Cell I.boundary) : I.boundary.grade d ≤ n + 3 := by
    simpa only [max_self] using I.grade_le d
  let all (d : Cell₀) : (scheme I).below (A, n + 3) :=
    ⟨d, (scheme I).scope_subset d, grade_bound I d⟩
  obtain ⟨r, hr, he⟩ := CanonicalRecursiveTopSections.exists_section I.rows I.proper
    n (height_le I) (hp.toBelow (A, n + 3))
  refine ⟨fun d => r (all d), hr.toRespects (fun d => (all d).2), ?_⟩
  intro d
  exact he ⟨d, I.boundary.scope_subset d, oldGrade d⟩

theorem joint_section {p} {q}
    (hp : RespectsSemantics I.left.rows p) (hq : RespectsSemantics I.right.rows q)
    (ha : ∀ i, p (I.shared.f i) = q (I.shared.g i)) :
    ∃ r , RespectsSemantics (rows I) r ∧
      (∀ d, r (left I d) = p d) ∧ ∀ d, r (right I d) = q d := by
  have hl := (PointImageSemantics.respects_iff I.left.scheme I.placeLeft I.imageLeft
    I.left.rows p).mpr hp
  have hr := (PointImageSemantics.respects_iff I.right.scheme I.placeRight I.imageRight
    I.right.rows q).mpr hq
  obtain ⟨u, hu, hul, hur⟩ :=
    (AmalgamatedBoundarySemantics.section_iff s I.leftScheme I.rightScheme I.shared
      I.planLeft I.planRight I.leftRows I.rightRows I.compatible hl hr).mpr ha
  obtain ⟨r, hrr, he⟩ := extend_boundary I hu
  exact ⟨r, hrr, fun d => (he _).trans (hul d), fun d => (he _).trans (hur d)⟩

/-- Stage bounding changes only newly supplied labels. Both complete input
faces, including literal tops, remain unchanged. -/
theorem joint_bounded {α} (hα : Order.IsSuccLimit α)
    {p} {q}
    (hp : RespectsSemantics I.left.rows p) (hq : RespectsSemantics I.right.rows q)
    (hpb : ∀ d, p d < ofOrd α ∨ p d = ⊤) (hqb : ∀ d, q d < ofOrd α ∨ q d = ⊤)
    (ha : ∀ i, p (I.shared.f i) = q (I.shared.g i)) :
    ∃ r , RespectsSemantics (rows I) r ∧
      (∀ d, r d < ofOrd α ∨ r d = ⊤) ∧
      (∀ d, r (left I d) = p d) ∧ ∀ d, r (right I d) = q d := by
  obtain ⟨r, hr, hl, hright⟩ := joint_section I hp hq ha
  refine ⟨fun d => truncExt α (r d), hr.truncate hα, fun d => truncExt_bound, ?_, ?_⟩
  · intro d
    change truncExt α (r (left I d)) = p d
    rw [hl]
    exact truncExt_id_of_bound (hpb d)
  · intro d
    change truncExt α (r (right I d)) = q d
    rw [hright]
    exact truncExt_id_of_bound (hqb d)

private theorem faceMap_label {α : Ordinal₀} {a b : ℕ}
    (p : S α b) (r : S α a) (f : Fin a ↪ Fin b)
    (hv : Finset.univ.image f ∈ p.scheme.scheme.plan)
    (hs : p.scheme.restrictFace f hv = r.scheme) (h : typeMap f p = some r)
    (d : Cell r.scheme.scheme) :
    p.label (SemSchemeBoundaryInput.faceMap p.scheme r.scheme f hv hs d) = r.label d := by simp_all [VaughtConjecture.Knight.typeMap] <;> aesop

/-- Compatibility of stage types supplies literal label agreement as well
as the shared scheme. No extra overlap-label equation is requested. -/
theorem compatible_labels {α : Ordinal₀} (C : CoatomPair (n + 2))
    {pa pb : S α (n + 3)} (h : C.Compatible pa pb) :
    let I := (CoatomBoundaryPresentation.of_compatible C h).input
    ∀ i, pa.label (I.shared.f i) = pb.label (I.shared.g i) := by
  dsimp 
  intro i
  let r := Classical.choose h
  have hl := (Classical.choose_spec h).1
  have hr := (Classical.choose_spec h).2
  exact (faceMap_label pa r C.g₁ _ _ hl i).trans (faceMap_label pb r C.g₂ _ _ hr i).symm

