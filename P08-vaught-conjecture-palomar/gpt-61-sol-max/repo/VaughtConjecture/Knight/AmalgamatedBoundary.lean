/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.AmalgamatedBoundaryPlan
import VaughtConjecture.Knight.ProfileBoundaryOrder

/-! # An ordered boundary on an arbitrary binary support plan

The constructor retains every occurrence of both old schemes, identifying
only the specified entire overlap. Both old orders and every inherited
lower domain are exact. Completeness is proved at every proper index.
Full-scope cells and their semantics are not supplied by this boundary.
-/

namespace VaughtConjecture.Knight.AmalgamatedBoundary

open AmalgamationPlan AmalgamatedBoundaryPlan

variable {ι : Type*} [DecidableEq ι]

/-- Put a scheme on an injective image of its point domain, without changing
its occurrence enumeration. -/
def pointImage {κ : Type*} [DecidableEq κ] {B : Finset ι} {C : Finset κ}
    (D : CellScheme B) (e : ι ↪ κ) (he : B.image e = C) : CellScheme C where
  plan := D.plan.image (Finset.image e)
  isPlan := he ▸ Plan.isPlan_image e D.isPlan
  card := D.card
  cell d := ((D.scope d).image e, D.grade d)
  cell_mem d := by
    obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp (D.cell_mem d)
    refine Plan.mem_gradedPlan.mpr ⟨Finset.mem_image.mpr ⟨_, hm, rfl⟩, hp, ?_⟩
    change D.grade d ≤ (D.scope d).card at hc
    simpa only [Finset.card_image_of_injective _ e.injective] using hc

theorem pointImage_complete {κ : Type*} [DecidableEq κ] {B : Finset ι} {C : Finset κ}
    (D : CellScheme B) (e : ι ↪ κ) (he : B.image e = C) (hD : D.IsComplete) :
    (pointImage D e he).IsComplete := by
  intro BJ hBJ
  obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp hBJ
  obtain ⟨K, hK, hKB⟩ := Finset.mem_image.mp hm
  have hj : BJ.2 ≤ K.card := by
    grind
  obtain ⟨d, hd⟩ := hD (K, BJ.2) (Plan.mem_gradedPlan.mpr ⟨hK, hp, hj⟩)
  refine ⟨d, ?_⟩
  change ((D.cell d).1.image e, (D.cell d).2) = BJ
  rw [hd]
  exact Prod.ext hKB rfl

/-- Exact shared occurrences of two ordered faces in one ambient point set.
The exhaustion fields concern geometry only, not labels or transformations. -/
structure Overlap {B C : Finset ι} (D : CellScheme B) (E : CellScheme C) (k : ℕ) where
  f : Fin k ↪ Cell D
  g : Fin k ↪ Cell E
  f_mono : StrictMono f
  g_mono : StrictMono g
  shared : ∀ i, D.cell (f i) = E.cell (g i)
  left_exhaustive : ∀ d, D.scope d ⊆ C → ∃ i, f i = d
  right_exhaustive : ∀ e, E.scope e ⊆ B → ∃ i, g i = e

variable {A : Finset ι} (s : Step A)
variable (D : CellScheme (A.erase s.a)) (E : CellScheme (A.erase s.b))
variable {k : ℕ} (w : Overlap D E k)

variable {s}

abbrev Boundary := ProfileFaceUnion.Carrier (X := Cell D) w.g

local notation "Boundary₀" => Boundary D E w

noncomputable def index : Boundary₀ → GradedIndex ι :=
  ProfileFaceUnion.paste w.g D.cell E.cell

local notation "index₀" => index D E w

theorem index_right e :
    index₀ (ProfileFaceUnion.right w.f w.g e) = E.cell e :=
  ProfileFaceUnion.paste_right w.shared e

variable (s)

theorem inside_left z (hz : (index₀ z).1 ⊆ A.erase s.a) :
    ∃ d, ProfileFaceUnion.left d = z := by
  rcases ProfileFaceUnion.covered w.f w.g z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · exact ⟨d, rfl⟩
  · rw [index_right] at hz
    obtain ⟨i, rfl⟩ := w.right_exhaustive e hz
    exact ⟨w.f i, (ProfileFaceUnion.right_shared w.f w.g i).symm⟩

theorem inside_right z (hz : (index₀ z).1 ⊆ A.erase s.b) :
    ∃ e, ProfileFaceUnion.right w.f w.g e = z := by
  rcases ProfileFaceUnion.covered w.f w.g z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · obtain ⟨i, rfl⟩ := w.left_exhaustive d hz
    exact ⟨w.g i, ProfileFaceUnion.right_shared w.f w.g i⟩
  · exact ⟨e, rfl⟩

theorem below_left d z :
    GradedLe (index₀ z) (D.cell d) ↔
      ∃ e : D.belowCell d, ProfileFaceUnion.left e.1 = z := by
  constructor
  · intro h
    obtain ⟨e, rfl⟩ := inside_left s D E w z
      (h.1.trans (D.scope_subset d))
    exact ⟨⟨e, h⟩, rfl⟩
  · rintro ⟨e, rfl⟩
    exact e.2

theorem below_right d z :
    GradedLe (index₀ z) (E.cell d) ↔
      ∃ e : E.belowCell d, ProfileFaceUnion.right w.f w.g e.1 = z := by
  constructor
  · intro h
    obtain ⟨e, rfl⟩ := inside_right s D E w z
      (h.1.trans (E.scope_subset d))
    rw [index_right] at h
    exact ⟨⟨e, h⟩, rfl⟩
  · grind [index_right]

theorem no_full z : (index₀ z).1 ≠ A := by
  rcases ProfileFaceUnion.covered w.f w.g z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · intro h
    have hs := D.scope_subset d
    change D.scope d = A at h
    rw [h] at hs
    exact Finset.notMem_erase s.a A (hs s.ha)
  · rw [index_right]
    intro h
    have hs := E.scope_subset e
    change E.scope e = A at h
    rw [h] at hs
    exact Finset.notMem_erase s.b A (hs s.hb)

variable (hD : D.plan = s.left) (hE : E.plan = s.right)

include hD hE in
theorem index_mem z : index₀ z ∈ Plan.gradedPlan s.plan := by
  rcases ProfileFaceUnion.covered w.f w.g z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp (D.cell_mem d)
    rw [hD] at hm
    exact Plan.mem_gradedPlan.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hm), hp, hc⟩
  · rw [index_right]
    obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp (E.cell_mem e)
    rw [hE] at hm
    exact Plan.mem_gradedPlan.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hm), hp, hc⟩

section
variable {s}

noncomputable def enumeration : Boundary₀ ≃ Fin (Fintype.card (Boundary₀)) :=
  ProfileBoundaryOrder.enumeration w.f_mono w.g_mono

end

local notation "enumeration₀" => enumeration D E w

/-- The ordered proper boundary, before installing full-scope cells. -/
noncomputable def scheme : CellScheme A where
  plan := s.plan
  isPlan := isPlan s
  card := Fintype.card (Boundary₀)
  cell d := index₀ ((enumeration₀).symm d)
  cell_mem _ := index_mem s D E w hD hE _

local notation "scheme₀" => scheme s D E w hD hE

theorem scope_proper c :
    (scheme₀).scope c ≠ A :=
  no_full s D E w ((enumeration₀).symm c)

noncomputable def leftCell (d : Cell D) : Cell (scheme₀) :=
  enumeration₀ (ProfileFaceUnion.left d)

noncomputable def rightCell (e : Cell E) : Cell (scheme₀) :=
  enumeration₀ (ProfileFaceUnion.right w.f w.g e)

local notation "leftCell₀" => leftCell s D E w hD hE

theorem left_index d :
    (scheme₀).cell (leftCell₀ d) = D.cell d := by
  change index₀ ((enumeration₀).symm (enumeration₀ _)) = _
  rw [Equiv.symm_apply_apply]
  rfl

local notation "rightCell₀" => rightCell s D E w hD hE

theorem right_index e :
    (scheme₀).cell (rightCell₀ e) = E.cell e := by
  change index₀ ((enumeration₀).symm (enumeration₀ _)) = _
  rw [Equiv.symm_apply_apply, index_right]

variable {s D E w hD hE} in
theorem left_order : StrictMono (leftCell₀) :=
  ProfileBoundaryOrder.enumeration_left

variable {s D E w hD hE} in
theorem right_order : StrictMono (rightCell₀) :=
  ProfileBoundaryOrder.enumeration_right

theorem left_exhaustive c
    (hc : (scheme₀).scope c ⊆ A.erase s.a) :
    ∃ d, leftCell₀ d = c := by
  obtain ⟨d, hd⟩ := inside_left s D E w ((enumeration₀).symm c) hc
  exact ⟨d, (congrArg enumeration₀ hd).trans ((enumeration₀).apply_symm_apply c)⟩

theorem right_exhaustive c
    (hc : (scheme₀).scope c ⊆ A.erase s.b) :
    ∃ e, rightCell₀ e = c := by
  obtain ⟨e, he⟩ := inside_right s D E w ((enumeration₀).symm c) hc
  exact ⟨e, (congrArg enumeration₀ he).trans ((enumeration₀).apply_symm_apply c)⟩

theorem overlap d e :
    leftCell₀ d = rightCell₀ e ↔
      ∃ i, w.f i = d ∧ w.g i = e := by
  change enumeration₀ _ = enumeration₀ _ ↔ _
  rw [Equiv.apply_eq_iff_eq]
  exact ProfileFaceUnion.overlap w.f w.g d e

noncomputable def leftBelow d : D.belowCell d ≃
    (scheme₀).below ((scheme₀).cell (leftCell₀ d)) :=
  Equiv.ofBijective (fun e => ⟨leftCell₀ e.1, by
    grind [left_index]⟩) ⟨by
    intro e f h
    exact Subtype.ext ((left_order).injective (congrArg Subtype.val h)), by
    intro e
    have he := e.2.trans (show GradedLe
      ((scheme₀).cell (leftCell₀ d)) (D.cell d) from by
      rw [left_index]
      exact GradedLe.refl _)
    obtain ⟨f, hf⟩ := (below_left s D E w d ((enumeration₀).symm e.1)).mp he
    exact ⟨f, Subtype.ext ((congrArg enumeration₀ hf).trans
      ((enumeration₀).apply_symm_apply e.1))⟩⟩

noncomputable def rightBelow d : E.belowCell d ≃
    (scheme₀).below ((scheme₀).cell (rightCell₀ d)) :=
  Equiv.ofBijective (fun e => ⟨rightCell₀ e.1, by
    grind [right_index]⟩) ⟨by
    intro e f h
    exact Subtype.ext ((right_order).injective (congrArg Subtype.val h)), by
    intro e
    have he := e.2.trans (show GradedLe
      ((scheme₀).cell (rightCell₀ d)) (E.cell d) from by
      rw [right_index]
      exact GradedLe.refl _)
    obtain ⟨f, hf⟩ := (below_right s D E w d ((enumeration₀).symm e.1)).mp he
    exact ⟨f, Subtype.ext ((congrArg enumeration₀ hf).trans
      ((enumeration₀).apply_symm_apply e.1))⟩⟩

/-- No new proper graded index is left uninhabited by the boundary. -/
theorem complete_proper (hDc : D.IsComplete) (hEc : E.IsComplete)
    {BJ} (hBJ : BJ ∈ Plan.gradedPlan s.plan) (hB : BJ.1 ≠ A) :
    ∃ c, (scheme₀).cell c = BJ := by
  rcases proper_index_cover s hBJ hB with hl | hr
  · rw [← hD] at hl
    obtain ⟨d, hd⟩ := hDc BJ hl
    exact ⟨leftCell₀ d, (left_index s D E w hD hE d).trans hd⟩
  · rw [← hE] at hr
    obtain ⟨e, he⟩ := hEc BJ hr
    exact ⟨rightCell₀ e, (right_index s D E w hD hE e).trans he⟩

