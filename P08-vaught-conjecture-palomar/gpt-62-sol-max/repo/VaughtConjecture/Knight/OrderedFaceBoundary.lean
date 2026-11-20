/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CellBelowEquiv
public import VaughtConjecture.Knight.ProfileBoundaryOrder

@[expose] public section

namespace VaughtConjecture.Knight.AmalgamatedBoundary

open AmalgamationPlan

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
    rw [← hKB, Finset.card_image_of_injective _ e.injective] at hc
    exact hc
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

end VaughtConjecture.Knight.AmalgamatedBoundary

namespace VaughtConjecture.Knight.OrderedFaceBoundary

open AmalgamationPlan

open AmalgamatedBoundary (Overlap)

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}

variable (D : CellScheme B) (E : CellScheme C)

variable {k : ℕ} (w : Overlap D E k)

abbrev Boundary := ProfileFaceUnion.Carrier (X := Cell D) w.g

noncomputable def index : Boundary D E w → Finset ι × ℕ :=
  ProfileFaceUnion.paste w.g D.cell E.cell

theorem index_right (e : Cell E) :
    index D E w (ProfileFaceUnion.right w.f w.g e) = E.cell e :=
  ProfileFaceUnion.paste_right w.f w.g w.shared e

theorem inside_left (z : Boundary D E w) (hz : (index D E w z).1 ⊆ B) :
    ∃ d, ProfileFaceUnion.left w.g d = z := by
  rcases ProfileFaceUnion.covered w.f w.g z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · exact ⟨d, rfl⟩
  · rw [index_right] at hz
    obtain ⟨i, rfl⟩ := w.right_exhaustive e hz
    exact ⟨w.f i, (ProfileFaceUnion.right_shared w.f w.g i).symm⟩

theorem inside_right (z : Boundary D E w) (hz : (index D E w z).1 ⊆ C) :
    ∃ e, ProfileFaceUnion.right w.f w.g e = z := by
  rcases ProfileFaceUnion.covered w.f w.g z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · obtain ⟨i, rfl⟩ := w.left_exhaustive d hz
    exact ⟨w.g i, ProfileFaceUnion.right_shared w.f w.g i⟩
  lia

variable (R : Finset (Finset ι)) (hR : Plan.IsPlan A R)

variable (hD : D.plan ⊆ R) (hE : E.plan ⊆ R)

include hD hE in
theorem index_mem (z : Boundary D E w) : index D E w z ∈ Plan.gradedPlan R := by
  rcases ProfileFaceUnion.covered w.f w.g z with ⟨d, rfl⟩ | ⟨e, rfl⟩
  · obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp (D.cell_mem d)
    exact Plan.mem_gradedPlan.mpr ⟨hD hm, hp, hc⟩
  · rw [index_right]
    obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp (E.cell_mem e)
    exact Plan.mem_gradedPlan.mpr ⟨hE hm, hp, hc⟩

noncomputable def enumeration : Boundary D E w ≃ Fin (Fintype.card (Boundary D E w)) :=
  ProfileBoundaryOrder.enumeration w.f w.g w.f_mono w.g_mono

/-- The ordered inherited boundary, with no mixed cells installed. -/
noncomputable def scheme : CellScheme A where
  plan := R
  isPlan := hR
  card := Fintype.card (Boundary D E w)
  cell d := index D E w ((enumeration D E w).symm d)
  cell_mem _ := index_mem D E w R hD hE _

noncomputable def leftCell (d : Cell D) : Cell (scheme D E w R hR hD hE) :=
  enumeration D E w (ProfileFaceUnion.left w.g d)

noncomputable def rightCell (e : Cell E) : Cell (scheme D E w R hR hD hE) :=
  enumeration D E w (ProfileFaceUnion.right w.f w.g e)

theorem left_index (d : Cell D) :
    (scheme D E w R hR hD hE).cell (leftCell D E w R hR hD hE d) = D.cell d := by
  change index D E w ((enumeration D E w).symm (enumeration D E w _)) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem right_index (e : Cell E) :
    (scheme D E w R hR hD hE).cell (rightCell D E w R hR hD hE e) = E.cell e := by
  change index D E w ((enumeration D E w).symm (enumeration D E w _)) = _
  rw [Equiv.symm_apply_apply, index_right]

theorem left_order : StrictMono (leftCell D E w R hR hD hE) :=
  ProfileBoundaryOrder.enumeration_left w.f w.g w.f_mono w.g_mono

theorem right_order : StrictMono (rightCell D E w R hR hD hE) :=
  ProfileBoundaryOrder.enumeration_right w.f w.g w.f_mono w.g_mono

theorem left_exhaustive (c : Cell (scheme D E w R hR hD hE))
    (hc : (scheme D E w R hR hD hE).scope c ⊆ B) :
    ∃ d, leftCell D E w R hR hD hE d = c := by
  obtain ⟨d, hd⟩ := inside_left D E w ((enumeration D E w).symm c) hc
  exact ⟨d, (congrArg (enumeration D E w) hd).trans
    ((enumeration D E w).apply_symm_apply c)⟩

theorem right_exhaustive (c : Cell (scheme D E w R hR hD hE))
    (hc : (scheme D E w R hR hD hE).scope c ⊆ C) :
    ∃ e, rightCell D E w R hR hD hE e = c := by
  obtain ⟨e, he⟩ := inside_right D E w ((enumeration D E w).symm c) hc
  exact ⟨e, (congrArg (enumeration D E w) he).trans
    (by grind)⟩

theorem overlap (d : Cell D) (e : Cell E) :
    leftCell D E w R hR hD hE d = rightCell D E w R hR hD hE e ↔
      ∃ i, w.f i = d ∧ w.g i = e := by
  change enumeration D E w _ = enumeration D E w _ ↔ _
  rw [Equiv.apply_eq_iff_eq]
  exact ProfileFaceUnion.overlap w.f w.g d e

/-- Completeness at an old index is inherited; new mixed indices are not claimed complete. -/
theorem complete_on_input (hDc : D.IsComplete) (hEc : E.IsComplete)
    {BJ : Finset ι × ℕ}
    (hBJ : BJ ∈ Plan.gradedPlan D.plan ∨ BJ ∈ Plan.gradedPlan E.plan) :
    ∃ c, (scheme D E w R hR hD hE).cell c = BJ := by
  rcases hBJ with hl | hr
  · obtain ⟨d, hd⟩ := hDc BJ hl
    exact ⟨leftCell D E w R hR hD hE d, (left_index D E w R hR hD hE d).trans hd⟩
  · obtain ⟨e, he⟩ := hEc BJ hr
    exact ⟨rightCell D E w R hR hD hE e, (right_index D E w R hR hD hE e).trans he⟩

end VaughtConjecture.Knight.OrderedFaceBoundary
