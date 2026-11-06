/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.OrderedFaceBoundary
import VaughtConjecture.Knight.AmalgamatedBoundaryRows

/-! # Literal semantics on two arbitrary ordered inherited faces

The two inherited tables are glued on their exact occurrence overlap.
No display is recoded and no faithful transformations are composed.
Only equality of the shared source rows is required for row installation.
Generalizes `AmalgamatedBoundaryRows` without requiring coatom geometry.
-/

namespace VaughtConjecture.Knight.OrderedFaceBoundaryRows

open AmalgamationPlan OrderedFaceBoundary  Value 
open AmalgamatedBoundary (Overlap)
open AmalgamatedBoundaryRows (total total_below pushRow pushRow_at pushRow_outside)

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
variable (D : CellScheme B) (E : CellScheme C)
variable {k : ℕ} (w : Overlap D E k)
variable (R : VaughtConjecture.AmalgamationPlan.SupportFamily ι) (hR : Plan.IsPlan A R)
variable (hD : D.plan ⊆ R) (hE : E.plan ⊆ R)
variable (semD : Semantics D) (semE : Semantics E)

local notation "K" => scheme D E w R hR hD hE
local notation "l" => leftCell D E w R hR hD hE
local notation "r" => rightCell D E w R hR hD hE

/-- Source equality on all shared occurrences, including every auxiliary. -/
def Compatible :=
  ∀ i j, total semD (w.f i) (w.f j) = total semE (w.g i) (w.g j)

def shared_cell i :=
  (overlap D E w R hR hD hE _ _).mpr ⟨i, rfl, rfl⟩

local notation "enumeration₀" => enumeration w

variable {D E w R hR hD hE} in
theorem covered c : (∃ d, l d = c) ∨ ∃ e, r e = c := by
  rcases ProfileFaceUnion.covered w.f w.g ((enumeration₀).symm c) with
    ⟨d, hd⟩ | ⟨e, he⟩
  · exact Or.inl ⟨d, (congrArg enumeration₀ hd).trans
      ((enumeration₀).apply_symm_apply c)⟩
  · exact Or.inr ⟨e, (congrArg enumeration₀ he).trans
      ((enumeration₀).apply_symm_apply c)⟩

local notation "leftBelow₀" => leftBelow D E w R hR hD hE

local notation "left_order₀" => left_order

local notation "right_order₀" => right_order

theorem pushRow_shared (hc : Compatible D E w semD semE) i :
    pushRow l semD (w.f i) = pushRow r semE (w.g i) := by
  funext z
  by_cases hz : GradedLe ((K).cell z) (D.cell (w.f i))
  · have hzl : GradedLe ((K).cell z) ((K).cell (l (w.f i))) := by
      rw [left_index]
      exact hz
    obtain ⟨d, hd⟩ := (leftBelow₀ (w.f i)).surjective ⟨z, hzl⟩
    have he : l d.1 = z := congrArg Subtype.val hd
    have hdc  := by
      have hs := d.2.1
      
      have hs' : (D.cell (w.f i)).1 ⊆ (E.cell (w.g i)).1 :=
        subset_of_eq (congrArg Prod.fst (w.shared i))
      exact hs.trans (hs'.trans (E.scope_subset _))
    obtain ⟨j, hj⟩ := w.left_exhaustive d.1 hdc
    rw [← he, ← hj, pushRow_at l (left_order₀).injective,
      shared_cell, pushRow_at r (right_order₀).injective]
    exact hc i j
  · rw [pushRow_outside l (left_order₀).injective
      (left_index D E w R hR hD hE) semD _ _ hz,
      pushRow_outside r (right_order₀).injective
      (right_index D E w R hR hD hE) semE]
    rwa [← w.shared]

noncomputable def table c :=
  ProfileFaceUnion.paste w.g (pushRow l semD) (pushRow r semE)
    ((enumeration₀).symm c)

local notation "table₀" => table D E w R hR hD hE semD semE

theorem table_left c d : table₀ (l c) (l d) =
    total semD c d := by
  change ProfileFaceUnion.paste w.g (pushRow l semD) (pushRow r semE)
    ((enumeration₀).symm
    (enumeration₀ (ProfileFaceUnion.left c))) (l d) = _
  rw [Equiv.symm_apply_apply]
  exact pushRow_at l (left_order₀).injective semD c d

theorem table_right (hc : Compatible D E w semD semE) c d :
    table₀ (r c) (r d) = total semE c d := by
  change ProfileFaceUnion.paste w.g (pushRow l semD) (pushRow r semE)
    ((enumeration₀).symm
    (enumeration₀ (ProfileFaceUnion.right w.f w.g c))) (r d) = _
  rw [Equiv.symm_apply_apply, ProfileFaceUnion.paste_right
    (pushRow_shared D E w R hR hD hE semD semE hc)]
  exact pushRow_at r (right_order₀).injective semE c d

variable (hc : Compatible D E w semD semE)

include hc in
theorem table_orderly c (d : (K).belowCell c) :
    table₀ c d.1 =
      extVisibilityReplace (table₀ c d.1)
        ((K).grade d.1) ((K).grade d.1) := by
  rcases covered c with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · obtain ⟨e, rfl⟩ := (leftBelow₀ c).surjective d
    change table₀ (l c) (l e.1) =
      extVisibilityReplace (table₀ (l c) (l e.1))
        ((K).cell (l e.1)).2 ((K).cell (l e.1)).2
    rw [table_left, total_below, left_index]
    exact semD.orderly c e
  · obtain ⟨e, rfl⟩ := (rightBelow D E w R hR hD hE c).surjective d
    change table₀ (r c) (r e.1) =
      extVisibilityReplace (table₀ (r c) (r e.1))
        ((K).cell (r e.1)).2 ((K).cell (r e.1)).2
    rw [table_right D E w R hR hD hE semD semE hc, total_below, right_index]
    exact semE.orderly c e

/-- Both rows are copied literally; the common rows agree by compatibility. -/
noncomputable def rows : Semantics K where
  E c d := table₀ c d.1
  orderly := table_orderly D E w R hR hD hE semD semE hc

theorem rows_left c d :
    (rows D E w R hR hD hE semD semE hc).E (l c) (leftBelow₀ c d) =
      semD.E c d :=
  (table_left D E w R hR hD hE semD semE c d.1).trans (total_below semD c d)

theorem rows_right c d :
    (rows D E w R hR hD hE semD semE hc).E (r c) (rightBelow D E w R hR hD hE c d) =
      semE.E c d :=
  (table_right D E w R hR hD hE semD semE hc c d.1).trans (total_below semE c d)

