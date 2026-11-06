module

public import Chazelle.Jordan.Jordan

/-!
# The abstract splitting lemma

Let `P`, `Q₁`, `Q₂` be simple polygons such that

* the boundaries of `Q₁` and `Q₂` lie in the filled region of `P` (`hb`),
* the boundary of `P` lies in the union of the boundaries of `Q₁` and `Q₂` (`hb'`),
* a point off all three boundaries is filled in `P` exactly when it is filled in exactly one
  of `Q₁`, `Q₂` (`hxor`).

Then (`split_filled`)

* `P.filled = Q₁.filled ∪ Q₂.filled`,
* the interiors of `Q₁.filled` and `Q₂.filled` are disjoint,
* `Q₁.filled ∩ Q₂.filled ⊆ Q₁.boundary ∩ Q₂.boundary`.

The proof: the common interior `I = (Q₁.filled \ Q₁.boundary) ∩ (Q₂.filled \ Q₂.boundary)` is
open, lies in `P.filledᶜ` (by `hxor`) and is relatively closed there (the filled regions are
closed, and a boundary point of `Q_i` is in `P.filled`); since `P.filledᶜ` is connected and
unbounded while `I` is bounded, `I = ∅`.  The remaining claims follow from `I = ∅` using
`boundary_subset_closure_interior`.
-/

namespace Chazelle.Existence

@[expose] public section

open Set Topology
open Chazelle.Jordan

/-- The filled region of a simple polygon lies in the closure of its interior. -/
theorem filled_subset_closure_interior {Q : Polygon} (hQ : Q.Simple) :
    Q.filled ⊆ closure (Q.filled \ Q.boundary) := by
  intro z hz
  by_cases hzb : z ∈ Q.boundary
  · exact boundary_subset_closure_interior hQ hzb
  · exact subset_closure ⟨hz, hzb⟩

/-- If the interiors of two simple polygons do not meet, then their filled regions meet only in
points of both boundaries. -/
theorem filled_inter_subset_of_interior_disjoint {Q₁ Q₂ : Polygon} (h₁ : Q₁.Simple)
    (h₂ : Q₂.Simple)
    (hI : (Q₁.filled \ Q₁.boundary) ∩ (Q₂.filled \ Q₂.boundary) = ∅) :
    Q₁.filled ∩ Q₂.filled ⊆ Q₁.boundary ∩ Q₂.boundary := by
  rintro z ⟨hz₁, hz₂⟩
  have key : ∀ (A B : Polygon), A.Simple → B.Simple →
      (A.filled \ A.boundary) ∩ (B.filled \ B.boundary) = ∅ →
      z ∈ A.filled → z ∈ B.filled → z ∈ A.boundary := by
    intro A B hA hB hAB hzA hzB
    by_contra hzb
    have hopen : IsOpen (A.filled \ A.boundary) := isOpen_filled_sdiff_boundary hA
    have hnhds : A.filled \ A.boundary ∈ 𝓝 z := hopen.mem_nhds ⟨hzA, hzb⟩
    have hcl : z ∈ closure (B.filled \ B.boundary) := filled_subset_closure_interior hB hzB
    obtain ⟨y, hy⟩ := mem_closure_iff_nhds.1 hcl _ hnhds
    simp_all
  grind

/-- The exterior of a simple polygon is not contained in the filled region of any polygon. -/
theorem filled_compl_not_subset_filled (P Q : Polygon) : ¬ P.filledᶜ ⊆ Q.filled := by
  intro h
  set w : Point := (max (coordBound P) (coordBound Q) + 1, 0) with hw
  have hP : coordBound P < w.1 := by
    grind
  have hQ : coordBound Q < w.1 := by
    grind
  exact far_not_mem_filled Q (Or.inl hQ) (h (far_not_mem_filled P (Or.inl hP)))

section
variable {P Q₁ Q₂ : Polygon} (hP : P.Simple) (h₁ : Q₁.Simple) (h₂ : Q₂.Simple) (hb : Q₁.boundary ∪ Q₂.boundary ⊆ P.filled) (hb' : P.boundary ⊆ Q₁.boundary ∪ Q₂.boundary) (hxor : ∀ z, z ∉ P.boundary → z ∉ Q₁.boundary → z ∉ Q₂.boundary →
      (z ∈ P.filled ↔ (z ∈ Q₁.filled ↔ z ∉ Q₂.filled)))
include P hP h₁ h₂ hb hb' hxor
/-- **The common interior is empty.**  Under the hypotheses of the splitting lemma, the
interiors of `Q₁` and `Q₂` do not meet. -/
theorem common_interior_empty :
    (Q₁.filled \ Q₁.boundary) ∩ (Q₂.filled \ Q₂.boundary) = ∅ := by
  set I := (Q₁.filled \ Q₁.boundary) ∩ (Q₂.filled \ Q₂.boundary) with hIdef
  -- `I` lies in the exterior of `P`
  have hIP : I ⊆ P.filledᶜ := by
    grind
  -- `I` is open
  have hIopen : IsOpen I :=
    (isOpen_filled_sdiff_boundary h₁).inter (isOpen_filled_sdiff_boundary h₂)
  -- `I` is relatively closed in the exterior of `P`
  have hIcl : closure I ∩ P.filledᶜ ⊆ I := by
    rintro z ⟨hzc, hzP⟩
    have hz₁ : z ∈ Q₁.filled :=
      (isClosed_filled Q₁).closure_subset (closure_mono (fun _ h => h.1.1) hzc)
    grind
  -- connectedness of the exterior
  by_contra hne
  rw [← Ne, ← nonempty_iff_ne_empty] at hne
  obtain ⟨z, hz⟩ := hne
  have hVopen : IsOpen (P.filledᶜ ∩ (closure I)ᶜ) :=
    (isOpen_filled_compl P).inter isClosed_closure.isOpen_compl
  have hdisj : Disjoint I (P.filledᶜ ∩ (closure I)ᶜ) :=
    Set.disjoint_left.2 fun x hx hx' => hx'.2 (subset_closure hx)
  have hcov : P.filledᶜ ⊆ I ∪ (P.filledᶜ ∩ (closure I)ᶜ) := by
    grind
  have hsub : P.filledᶜ ⊆ I :=
    IsPreconnected.subset_left_of_subset_union hIopen hVopen hdisj hcov ⟨z, hIP hz, hz⟩
      (filled_compl_connected hP)
  exact filled_compl_not_subset_filled P Q₁ (fun x hx => (hsub hx).1.1)

/-- **The splitting lemma.**  Let `P`, `Q₁`, `Q₂` be simple polygons with the boundaries of
`Q₁`, `Q₂` inside `P.filled`, the boundary of `P` inside the union of the boundaries of `Q₁`
and `Q₂`, and such that every point off all three boundaries is filled in `P` exactly when it
is filled in exactly one of `Q₁`, `Q₂`.  Then the filled region of `P` is the union of the
filled regions of `Q₁` and `Q₂`, the interiors of the latter are disjoint, and the filled
regions of `Q₁` and `Q₂` meet only in points of both boundaries. -/
theorem split_filled :
    P.filled = Q₁.filled ∪ Q₂.filled ∧
      Disjoint (interior Q₁.filled) (interior Q₂.filled) ∧
      Q₁.filled ∩ Q₂.filled ⊆ Q₁.boundary ∩ Q₂.boundary := by
  have hI := common_interior_empty hP h₁ h₂ hb hb' hxor
  have hmeet := filled_inter_subset_of_interior_disjoint h₁ h₂ hI
  refine ⟨?_, ?_, hmeet⟩
  · apply Subset.antisymm
    · intro z hz
      by_cases hzP : z ∈ P.boundary
      · rcases hb' hzP with h | h
        · exact Or.inl (boundary_subset_filled Q₁ h)
        · exact Or.inr (boundary_subset_filled Q₂ h)
      by_cases hz₁ : z ∈ Q₁.boundary
      · exact Or.inl (boundary_subset_filled Q₁ hz₁)
      by_cases hz₂ : z ∈ Q₂.boundary
      · exact Or.inr (boundary_subset_filled Q₂ hz₂)
      grind
    · intro z hz
      by_cases hzP : z ∈ P.boundary
      · grind
      by_cases hz₁ : z ∈ Q₁.boundary
      · grind
      by_cases hz₂ : z ∈ Q₂.boundary
      · grind
      
      rcases hz with hzf | hzf
      · have hz₂f : z ∉ Q₂.filled := fun h' => hz₁ (hmeet ⟨hzf, h'⟩).1
        simp_all
      · have hz₁f : z ∉ Q₁.filled := fun h' => hz₂ (hmeet ⟨h', hzf⟩).2
        simp_all
  · rw [interior_filled h₁, interior_filled h₂, Set.disjoint_iff_inter_eq_empty]
    exact hI

/-- The filled region of `P` is the union of the filled regions of `Q₁` and `Q₂`
(first conclusion of `split_filled`). -/
theorem split_filled_eq_union :
    P.filled = Q₁.filled ∪ Q₂.filled :=
  (split_filled hP h₁ h₂ hb hb' hxor).1

/-- The interiors of the filled regions of `Q₁` and `Q₂` are disjoint
(second conclusion of `split_filled`). -/
theorem split_interior_disjoint :
    Disjoint (interior Q₁.filled) (interior Q₂.filled) :=
  (split_filled hP h₁ h₂ hb hb' hxor).2.1

/-- The filled regions of `Q₁` and `Q₂` meet only in points of both boundaries
(third conclusion of `split_filled`). -/
theorem split_filled_inter_subset :
    Q₁.filled ∩ Q₂.filled ⊆ Q₁.boundary ∩ Q₂.boundary :=
  (split_filled hP h₁ h₂ hb hb' hxor).2.2


end

end

end Chazelle.Existence
