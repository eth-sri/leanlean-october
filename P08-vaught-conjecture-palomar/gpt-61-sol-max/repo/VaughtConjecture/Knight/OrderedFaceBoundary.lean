/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.AmalgamatedBoundary

/-! # Ordered inherited boundary for two arbitrary visible faces

Generalizes the occurrence construction of `AmalgamatedBoundary` beyond coatom
geometry. The common plan is supplied, every occurrence of both inputs is retained,
and exactly the specified overlap is identified. Both original orders and complete
lower domains are preserved. No cells at new mixed indices are constructed here.

This is the ordered-boundary part of new25, not a receiving probe.
-/

namespace VaughtConjecture.Knight.OrderedFaceBoundary

open AmalgamationPlan
open AmalgamatedBoundary (Overlap)

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
variable (D : CellScheme B) (E : CellScheme C)
variable {k : ℕ} (w : Overlap D E k)

abbrev Boundary := ProfileFaceUnion.Carrier (X := Cell D) w.g

local notation "Boundary₀" => Boundary D E w

noncomputable def index : Boundary₀ → GradedIndex ι :=
  ProfileFaceUnion.paste w.g D.cell E.cell

local notation "index₀" => index D E w

theorem index_right e :
    index₀ (ProfileFaceUnion.right w.f w.g e) = E.cell e :=
  ProfileFaceUnion.paste_right w.shared e

theorem inside_left z (hz : (index₀ z).1 ⊆ B) :
    ∃ d, ProfileFaceUnion.left d = z := by
  rcases ProfileFaceUnion.covered w.f w.g z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · exact ⟨d, rfl⟩
  · rw [index_right] at hz
    obtain ⟨i, rfl⟩ := w.right_exhaustive e hz
    exact ⟨w.f i, (ProfileFaceUnion.right_shared w.f w.g i).symm⟩

theorem inside_right z (hz : (index₀ z).1 ⊆ C) :
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
    obtain ⟨e, rfl⟩ := inside_left D E w z
      (h.1.trans (D.scope_subset d))
    exact ⟨⟨e, h⟩, rfl⟩
  · rintro ⟨e, rfl⟩
    exact e.2

theorem below_right d z :
    GradedLe (index₀ z) (E.cell d) ↔
      ∃ e : E.belowCell d, ProfileFaceUnion.right w.f w.g e.1 = z := by
  constructor
  · intro h
    obtain ⟨e, rfl⟩ := inside_right D E w z
      (h.1.trans (E.scope_subset d))
    rw [index_right] at h
    exact ⟨⟨e, h⟩, rfl⟩
  · grind [index_right]

variable (R : VaughtConjecture.AmalgamationPlan.SupportFamily ι) (hR : Plan.IsPlan A R)
variable (hD : D.plan ⊆ R) (hE : E.plan ⊆ R)

include hD hE in
theorem index_mem z : index₀ z ∈ Plan.gradedPlan R := by
  rcases ProfileFaceUnion.covered w.f w.g z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp (D.cell_mem d)
    exact Plan.mem_gradedPlan.mpr ⟨hD hm, hp, hc⟩
  · rw [index_right]
    obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp (E.cell_mem e)
    exact Plan.mem_gradedPlan.mpr ⟨hE hm, hp, hc⟩

variable {D E} in
noncomputable def enumeration : Boundary₀ ≃ Fin (Fintype.card (Boundary₀)) :=
  ProfileBoundaryOrder.enumeration w.f_mono w.g_mono

local notation "enumeration₀" => enumeration w

/-- The ordered inherited boundary, with no mixed cells installed. -/
noncomputable def scheme : CellScheme A where
  plan := R
  isPlan := hR
  card := Fintype.card (Boundary₀)
  cell d := index₀ ((enumeration₀).symm d)
  cell_mem _ := index_mem D E w R hD hE _

local notation "scheme₀" => scheme D E w R hR hD hE

noncomputable def leftCell (d : Cell D) : Cell (scheme₀) :=
  enumeration₀ (ProfileFaceUnion.left d)

noncomputable def rightCell (e : Cell E) : Cell (scheme₀) :=
  enumeration₀ (ProfileFaceUnion.right w.f w.g e)

local notation "leftCell₀" => leftCell D E w R hR hD hE

theorem left_index d :
    (scheme₀).cell (leftCell₀ d) = D.cell d := by
  change index₀ ((enumeration₀).symm (enumeration₀ _)) = _
  rw [Equiv.symm_apply_apply]
  rfl

local notation "rightCell₀" => rightCell D E w R hR hD hE

theorem right_index e :
    (scheme₀).cell (rightCell₀ e) = E.cell e := by
  change index₀ ((enumeration₀).symm (enumeration₀ _)) = _
  rw [Equiv.symm_apply_apply, index_right]

variable {D E w R hR hD hE} in
theorem left_order : StrictMono (leftCell₀) :=
  ProfileBoundaryOrder.enumeration_left

variable {D E w R hR hD hE} in
theorem right_order : StrictMono (rightCell₀) :=
  ProfileBoundaryOrder.enumeration_right

theorem left_exhaustive c
    (hc : (scheme₀).scope c ⊆ B) :
    ∃ d, leftCell₀ d = c := by
  obtain ⟨d, hd⟩ := inside_left D E w ((enumeration₀).symm c) hc
  exact ⟨d, (congrArg enumeration₀ hd).trans
    ((enumeration₀).apply_symm_apply c)⟩

theorem right_exhaustive c
    (hc : (scheme₀).scope c ⊆ C) :
    ∃ e, rightCell₀ e = c := by
  obtain ⟨e, he⟩ := inside_right D E w ((enumeration₀).symm c) hc
  exact ⟨e, (congrArg enumeration₀ he).trans
    ((enumeration₀).apply_symm_apply c)⟩

theorem overlap d e :
    leftCell₀ d = rightCell₀ e ↔
      ∃ i, w.f i = d ∧ w.g i = e := by
  change enumeration₀ _ = enumeration₀ _ ↔ _
  rw [Equiv.apply_eq_iff_eq]
  exact ProfileFaceUnion.overlap w.f w.g d e

noncomputable def leftBelow d : D.belowCell d ≃
    (scheme₀).below
      ((scheme₀).cell (leftCell₀ d)) :=
  Equiv.ofBijective (fun e => ⟨leftCell₀ e.1, by
    grind [left_index]⟩) ⟨by
    intro e f h
    exact Subtype.ext ((left_order).injective (congrArg Subtype.val h)), by
    intro e
    have he := e.2.trans (show GradedLe
      ((scheme₀).cell (leftCell₀ d)) (D.cell d) from by
      rw [left_index]
      exact GradedLe.refl _)
    obtain ⟨f, hf⟩ := (below_left D E w d ((enumeration₀).symm e.1)).mp he
    exact ⟨f, Subtype.ext ((congrArg enumeration₀ hf).trans
      ((enumeration₀).apply_symm_apply e.1))⟩⟩

noncomputable def rightBelow d : E.belowCell d ≃
    (scheme₀).below
      ((scheme₀).cell (rightCell₀ d)) :=
  Equiv.ofBijective (fun e => ⟨rightCell₀ e.1, by
    grind [right_index]⟩) ⟨by
    intro e f h
    exact Subtype.ext ((right_order).injective (congrArg Subtype.val h)), by
    intro e
    have he := e.2.trans (show GradedLe
      ((scheme₀).cell (rightCell₀ d)) (E.cell d) from by
      rw [right_index]
      exact GradedLe.refl _)
    obtain ⟨f, hf⟩ := (below_right D E w d ((enumeration₀).symm e.1)).mp he
    exact ⟨f, Subtype.ext ((congrArg enumeration₀ hf).trans
      ((enumeration₀).apply_symm_apply e.1))⟩⟩

/-- Completeness at an old index is inherited; new mixed indices are not claimed complete. -/
theorem complete_on_input (hDc : D.IsComplete) (hEc : E.IsComplete)
    {BJ}
    (hBJ : BJ ∈ Plan.gradedPlan D.plan ∨ BJ ∈ Plan.gradedPlan E.plan) :
    ∃ c, (scheme₀).cell c = BJ := by
  rcases hBJ with hl | hr
  · obtain ⟨d, hd⟩ := hDc BJ hl
    exact ⟨leftCell₀ d, (left_index D E w R hR hD hE d).trans hd⟩
  · obtain ⟨e, he⟩ := hEc BJ hr
    exact ⟨rightCell₀ e, (right_index D E w R hR hD hE e).trans he⟩

