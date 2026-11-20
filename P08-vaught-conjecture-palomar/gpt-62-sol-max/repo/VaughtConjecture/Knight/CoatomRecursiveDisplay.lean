/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoatomRecursiveInput
public import VaughtConjecture.Knight.CanonicalRecursiveTopSections
public import VaughtConjecture.Knight.Coface

@[expose] public section

namespace VaughtConjecture.Knight.CoatomRecursiveDisplay

open AmalgamationPlan AmalgamatedBoundaryPlan SemSchemeBoundaryInput

open Transform Value ExtOrd CoatomRecursiveInput

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {s : Step A}

variable {m n : ℕ} (I : Input s m (n + 3) (n + 3))

abbrev boundary := CanonicalRecursiveContract.boundary I.rows n (height_le I)

abbrev left (d : Cell I.left.scheme) : Cell (scheme I) :=
  boundary I (I.leftFace.map d)

abbrev right (d : Cell I.right.scheme) : Cell (scheme I) :=
  boundary I (I.rightFace.map d)

/-- The literal-top section theorem now covers the entire output inventory. -/
theorem extend_boundary {p : Cell I.boundary → ExtOrd} (hp : RespectsSemantics I.rows p) :
    ∃ r : Cell (scheme I) → ExtOrd, RespectsSemantics (rows I) r ∧
      ∀ d, r (boundary I d) = p d := by
  have oldGrade (d : Cell I.boundary) : I.boundary.grade d ≤ n + 3 := by
    simpa [max_self] using I.grade_le d
  let all (d : Cell (scheme I)) : (scheme I).below (A, n + 3) :=
    ⟨d, (scheme I).scope_subset d, grade_bound I d⟩
  obtain ⟨r, hr, he⟩ := CanonicalRecursiveTopSections.exists_section I.rows I.proper
    n (height_le I) (hp.toBelow (A, n + 3))
  refine ⟨fun d => r (all d), hr.toRespects (fun d => (all d).2), ?_⟩
  intro d
  exact he ⟨d, I.boundary.scope_subset d, oldGrade d⟩

theorem joint_section {p : Cell I.left.scheme → ExtOrd} {q : Cell I.right.scheme → ExtOrd}
    (hp : RespectsSemantics I.left.rows p) (hq : RespectsSemantics I.right.rows q)
    (ha : ∀ i, p (I.shared.f i) = q (I.shared.g i)) :
    ∃ r : Cell (scheme I) → ExtOrd, RespectsSemantics (rows I) r ∧
      (∀ d, r (left I d) = p d) ∧ ∀ d, r (right I d) = q d := by
  obtain ⟨r, hrr, he⟩ := extend_boundary I (I.paste_respects hp hq ha)
  exact ⟨r, hrr, fun d => (he _).trans (I.paste_left p q d), fun d => (he _).trans (I.paste_right p q ha d)⟩

/-- Stage bounding changes only newly supplied labels. Both complete input
faces, including literal tops, remain unchanged. -/
theorem joint_bounded {α : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    {p : Cell I.left.scheme → ExtOrd} {q : Cell I.right.scheme → ExtOrd}
    (hp : RespectsSemantics I.left.rows p) (hq : RespectsSemantics I.right.rows q)
    (hpb : ∀ d, p d < ofOrd α ∨ p d = ⊤) (hqb : ∀ d, q d < ofOrd α ∨ q d = ⊤)
    (ha : ∀ i, p (I.shared.f i) = q (I.shared.g i)) :
    ∃ r : Cell (scheme I) → ExtOrd, RespectsSemantics (rows I) r ∧
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

end

end VaughtConjecture.Knight.CoatomRecursiveDisplay
